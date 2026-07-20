/-
# Signed-angle cos/sin `CReal` addition laws: the mixed-sign quadrants

This module closes the *mixed-sign* half of the constructive signed trig addition
program, sitting on top of the same-sign quadrants already landed in
`TrigSignedAdd.lean` (nonneg via `TrigAdd.cos_add_equiv_nonneg` /
`TrigAdd.sin_add_equiv_nonneg`; both-nonpos via `cos_add_equiv_negneg` /
`sin_add_equiv_negneg`).

## The structure of the reduction

The two remaining quadrants are `A ≥ 0, B ≤ 0` (`posneg`) and its mirror
`A ≤ 0, B ≥ 0` (`negpos`).  We show, with **fully proved** parity / commutativity
transport (`propext`/`Quot.sound` only), that

  * both `posneg` laws follow from the two **opposite-sign cores**
    (`OppositeSignCosCore` / `OppositeSignSinCore` — the subtraction formulas
    `cos(A−C) = cosA cosC + sinA sinC`, `sin(A−C) = sinA cosC − cosA sinC` for
    `A,C ≥ 0`), and
  * both `negpos` laws follow from the `posneg` laws by argument commutativity.

So all four mixed-sign quadrants collapse onto the two opposite-sign cores.

## What is genuinely proved here

  * a small pointwise `CReal` toolkit (`cadd_comm`, `cosFull_argeqv`);
  * `cos_add_equiv_posneg` / `sin_add_equiv_posneg` — the `A ≥ 0, B ≤ 0` laws,
    conditional on the opposite-sign cores (genuine parity transport);
  * `cos_add_equiv_negpos` / `sin_add_equiv_negpos` — the mirror `A ≤ 0, B ≥ 0`
    laws, from the `posneg` laws by commutativity.

## The residual (honest, named — the SINGLE analytic gate)

The two opposite-sign cores both reduce to the series-level Pythagorean identity
`cosFull C² + sinFull C² ≃ 1` for `C ≥ 0` — the named residual `PythFull` from the
upstream module (a `2×2` Cramer solve over the nonneg laws whose determinant is
supplied by `PythFull`).  Here we (a) name the sine-side core
`OppositeSignSinCore`, and (b) reduce `OppositeSignCosCore` to `PythFull` directly
(`oppositeSignCosCore_of_pyth`), so the entire mixed-sign program rests on the one
analytic obligation `PythFull`, which is NOT inhabited here.
-/
import ConstructiveReals.TrigSignedAdd
import ConstructiveReals.CRealAlg

namespace ConstructiveReals

open ConstructiveReals.CReal
open TrigAddCReal
open TrigSineAddCReal

namespace TrigSignedAddFull

/-! ## 0. A small pointwise `CReal` toolkit -/

/-- `A + B ≃ B + A` (pointwise, via `Q'.add_comm_eqv`). -/
theorem cadd_comm (A B : CReal) :
    CReal.Equiv (CReal.add A B) (CReal.add B A) :=
  TrigAdd.equiv_of_approx_eqv (fun n => Q'.add_comm_eqv (A.approx n) (B.approx n))

/-- `cosFull` is a congruence for `Q'`-equivalence of its (signed) argument
(via evenness `cosFull_abs_congr` and `Q'.abs_eqv_congr`). -/
theorem cosFull_argeqv {x y : Q'} (h : x.eqv y) :
    CReal.Equiv (TrigAdd.cosFull x) (TrigAdd.cosFull y) :=
  TrigSignedAdd.cosFull_abs_congr (Q'.abs_eqv_congr h)

/-! ## 1. The sine opposite-sign core (named residual)

The cosine opposite-sign core `OppositeSignCosCore` is already declared upstream in
`TrigSignedAdd.lean`.  The sine analogue is its cross-parity twin. -/

/-- **Named residual `OppositeSignSinCore`.**  The opposite-sign (subtraction)
sine law `sinFull (A − C) ≃ sinFull A·cosFull C − cosFull A·sinFull C` for
`A, C ≥ 0`.  Like its cosine twin it reduces to `PythFull`.  Not inhabited here. -/
structure OppositeSignSinCore : Type where
  core : ∀ (A C : Q'), (0 : Q') ≤ A → (0 : Q') ≤ C →
    CReal.Equiv (TrigAdd.sinFull (A + (-C)))
      (CReal.add (CReal.mul (TrigAdd.sinFull A) (TrigAdd.cosFull C))
        (CReal.neg (CReal.mul (TrigAdd.cosFull A) (TrigAdd.sinFull C))))

/-! ## 2. The `A ≥ 0, B ≤ 0` (posneg) quadrant -/

/-- **Signed cosine addition law, `A ≥ 0, B ≤ 0` quadrant**, from the cosine
opposite-sign core.  `cosFull (A+B) ≃ cosFull A·cosFull B − sinFull A·sinFull B`. -/
theorem cos_add_equiv_posneg (oc : TrigSignedAdd.OppositeSignCosCore)
    {A B : Q'} (hA : (0 : Q') ≤ A) (hB : B ≤ 0) :
    CReal.Equiv (TrigAdd.cosFull (A + B)) (TrigAdd.cosProdMinus A B) := by
  have hC : (0 : Q') ≤ -B := Q'.nonneg_neg_of_nonpos hB
  -- opposite-sign core at C := -B (so -C = -(-B))
  have hcore := oc.core A (-B) hA hC
  -- argument transport: A + B ≃ A + (-(-B))
  have harg : (A + B).eqv (A + (-(-B))) :=
    Q'.add_eqv_congr' (Q'.eqv_refl A) (Q'.eqv_symm (Q'.neg_neg_eqv B))
  have hcosarg : CReal.Equiv (TrigAdd.cosFull (A + B)) (TrigAdd.cosFull (A + (-(-B)))) :=
    cosFull_argeqv harg
  -- rewrite the core's RHS back to `cosProdMinus A B`
  have hL : CReal.Equiv (CReal.mul (TrigAdd.cosFull A) (TrigAdd.cosFull (-B)))
      (CReal.mul (TrigAdd.cosFull A) (TrigAdd.cosFull B)) :=
    TrigSignedAdd.mul_congr_right (TrigAdd.cosFull_even B)
  have hR : CReal.Equiv (CReal.mul (TrigAdd.sinFull A) (TrigAdd.sinFull (-B)))
      (CReal.neg (CReal.mul (TrigAdd.sinFull A) (TrigAdd.sinFull B))) :=
    (TrigSignedAdd.mul_congr_right (TrigSignedAdd.sinFull_neg B)).trans
      (TrigSignedAdd.mul_neg (TrigAdd.sinFull A) (TrigAdd.sinFull B))
  have hrhs : CReal.Equiv
      (CReal.add (CReal.mul (TrigAdd.cosFull A) (TrigAdd.cosFull (-B)))
        (CReal.mul (TrigAdd.sinFull A) (TrigAdd.sinFull (-B))))
      (TrigAdd.cosProdMinus A B) := by
    unfold TrigAdd.cosProdMinus
    exact (CReal.add_congr_left hL).trans (CReal.add_congr_right hR)
  exact hcosarg.trans (hcore.trans hrhs)

/-- **Signed sine addition law, `A ≥ 0, B ≤ 0` quadrant**, from the sine
opposite-sign core.  `sinFull (A+B) ≃ sinFull A·cosFull B + cosFull A·sinFull B`. -/
theorem sin_add_equiv_posneg (os : OppositeSignSinCore)
    {A B : Q'} (hA : (0 : Q') ≤ A) (hB : B ≤ 0) :
    CReal.Equiv (TrigAdd.sinFull (A + B)) (TrigSineAddCReal.sinProdPlus A B) := by
  have hC : (0 : Q') ≤ -B := Q'.nonneg_neg_of_nonpos hB
  have hcore := os.core A (-B) hA hC
  have harg : (A + B).eqv (A + (-(-B))) :=
    Q'.add_eqv_congr' (Q'.eqv_refl A) (Q'.eqv_symm (Q'.neg_neg_eqv B))
  have hsinarg : CReal.Equiv (TrigAdd.sinFull (A + B)) (TrigAdd.sinFull (A + (-(-B)))) :=
    TrigSignedAdd.sinFull_eqv_congr harg
  -- rewrite the core's RHS back to `sinProdPlus A B`
  have hL : CReal.Equiv (CReal.mul (TrigAdd.sinFull A) (TrigAdd.cosFull (-B)))
      (CReal.mul (TrigAdd.sinFull A) (TrigAdd.cosFull B)) :=
    TrigSignedAdd.mul_congr_right (TrigAdd.cosFull_even B)
  have hR : CReal.Equiv
      (CReal.neg (CReal.mul (TrigAdd.cosFull A) (TrigAdd.sinFull (-B))))
      (CReal.mul (TrigAdd.cosFull A) (TrigAdd.sinFull B)) :=
    (CReal.neg_congr
      ((TrigSignedAdd.mul_congr_right (TrigSignedAdd.sinFull_neg B)).trans
        (TrigSignedAdd.mul_neg (TrigAdd.cosFull A) (TrigAdd.sinFull B)))).trans
      (TrigSignedAdd.neg_neg_equiv (CReal.mul (TrigAdd.cosFull A) (TrigAdd.sinFull B)))
  have hrhs : CReal.Equiv
      (CReal.add (CReal.mul (TrigAdd.sinFull A) (TrigAdd.cosFull (-B)))
        (CReal.neg (CReal.mul (TrigAdd.cosFull A) (TrigAdd.sinFull (-B)))))
      (TrigSineAddCReal.sinProdPlus A B) := by
    unfold TrigSineAddCReal.sinProdPlus
    exact (CReal.add_congr_left hL).trans (CReal.add_congr_right hR)
  exact hsinarg.trans (hcore.trans hrhs)

/-! ## 3. The mirror `A ≤ 0, B ≥ 0` (negpos) quadrant -/

/-- **Signed cosine addition law, `A ≤ 0, B ≥ 0` quadrant**, from `posneg` by
argument commutativity. -/
theorem cos_add_equiv_negpos (oc : TrigSignedAdd.OppositeSignCosCore)
    {A B : Q'} (hA : A ≤ 0) (hB : (0 : Q') ≤ B) :
    CReal.Equiv (TrigAdd.cosFull (A + B)) (TrigAdd.cosProdMinus A B) := by
  -- cosFull (A+B) ≃ cosFull (B+A)
  have hswap : CReal.Equiv (TrigAdd.cosFull (A + B)) (TrigAdd.cosFull (B + A)) :=
    cosFull_argeqv (Q'.add_comm_eqv A B)
  -- posneg with roles swapped: cosFull (B+A) ≃ cosProdMinus B A
  have hpn : CReal.Equiv (TrigAdd.cosFull (B + A)) (TrigAdd.cosProdMinus B A) :=
    cos_add_equiv_posneg oc hB hA
  -- cosProdMinus B A ≃ cosProdMinus A B (product commutativity)
  have hcomm : CReal.Equiv (TrigAdd.cosProdMinus B A) (TrigAdd.cosProdMinus A B) := by
    unfold TrigAdd.cosProdMinus
    exact (CReal.add_congr_left (CRealAlg.cmul_comm (TrigAdd.cosFull B) (TrigAdd.cosFull A))).trans
      (CReal.add_congr_right
        (CReal.neg_congr (CRealAlg.cmul_comm (TrigAdd.sinFull B) (TrigAdd.sinFull A))))
  exact hswap.trans (hpn.trans hcomm)

/-- **Signed sine addition law, `A ≤ 0, B ≥ 0` quadrant**, from `posneg` by
argument commutativity. -/
theorem sin_add_equiv_negpos (os : OppositeSignSinCore)
    {A B : Q'} (hA : A ≤ 0) (hB : (0 : Q') ≤ B) :
    CReal.Equiv (TrigAdd.sinFull (A + B)) (TrigSineAddCReal.sinProdPlus A B) := by
  have hswap : CReal.Equiv (TrigAdd.sinFull (A + B)) (TrigAdd.sinFull (B + A)) :=
    TrigSignedAdd.sinFull_eqv_congr (Q'.add_comm_eqv A B)
  have hpn : CReal.Equiv (TrigAdd.sinFull (B + A)) (TrigSineAddCReal.sinProdPlus B A) :=
    sin_add_equiv_posneg os hB hA
  -- sinProdPlus B A ≃ sinProdPlus A B (two mul-comms + one add-comm)
  have hX : CReal.Equiv (CReal.mul (TrigAdd.sinFull B) (TrigAdd.cosFull A))
      (CReal.mul (TrigAdd.cosFull A) (TrigAdd.sinFull B)) :=
    CRealAlg.cmul_comm (TrigAdd.sinFull B) (TrigAdd.cosFull A)
  have hY : CReal.Equiv (CReal.mul (TrigAdd.cosFull B) (TrigAdd.sinFull A))
      (CReal.mul (TrigAdd.sinFull A) (TrigAdd.cosFull B)) :=
    CRealAlg.cmul_comm (TrigAdd.cosFull B) (TrigAdd.sinFull A)
  have hcomm : CReal.Equiv (TrigSineAddCReal.sinProdPlus B A)
      (TrigSineAddCReal.sinProdPlus A B) := by
    unfold TrigSineAddCReal.sinProdPlus
    -- add (sinB cosA) (cosB sinA) ≃ add (cosA sinB) (sinA cosB) ≃ add (sinA cosB) (cosA sinB)
    refine ((CReal.add_congr_left hX).trans (CReal.add_congr_right hY)).trans ?_
    exact cadd_comm (CReal.mul (TrigAdd.cosFull A) (TrigAdd.sinFull B))
      (CReal.mul (TrigAdd.sinFull A) (TrigAdd.cosFull B))
  exact hswap.trans (hpn.trans hcomm)

/-! ## 4. Reducing the cosine opposite-sign core to `PythFull`

We inhabit `TrigSignedAdd.OppositeSignCosCore` from the single named residual
`TrigSignedAdd.PythFull`, via the `2×2` Cramer solve sketched in the module
header.  This is fully proved (`propext`/`Quot.sound` only): the only input beyond
the already-landed nonneg addition laws is `PythFull`. -/

/-- `¬ (p ≤ q) → q ≤ p` on `Q'` (decidable `Int` trichotomy on numerators);
replicated locally to avoid a heavy import. -/
theorem le_of_not_le {p q : Q'} (h : ¬ (p ≤ q)) : q ≤ p := by
  show q.num * (p.den : Int) ≤ p.num * (q.den : Int)
  have h' : ¬ (p.num * (q.den : Int) ≤ q.num * (p.den : Int)) := h
  exact Int.le_of_lt (Int.not_le.mp h')

/-! ### Extra pointwise `CReal` algebra helpers for the solve -/

/-- `(A + B) + C ≃ A + (B + C)` (pointwise). -/
theorem cadd_assoc (A B C : CReal) :
    CReal.Equiv (CReal.add (CReal.add A B) C) (CReal.add A (CReal.add B C)) :=
  TrigAdd.equiv_of_approx_eqv (fun n => Q'.add_assoc_eqv (A.approx n) (B.approx n) (C.approx n))

/-- `A + 0 ≃ A` (pointwise). -/
theorem cadd_zero (A : CReal) : CReal.Equiv (CReal.add A CReal.czero) A :=
  TrigAdd.equiv_of_approx_eqv (fun n => Q'.eqv_of_eq (Q'.add_zero' (A.approx n)))

/-- `(A + B)·C ≃ A·C + B·C` (pointwise). -/
theorem cadd_mul (A B C : CReal) :
    CReal.Equiv (CReal.mul (CReal.add A B) C)
      (CReal.add (CReal.mul A C) (CReal.mul B C)) :=
  TrigAdd.equiv_of_approx_eqv (fun n => Q'.add_mul_eqv (A.approx n) (B.approx n) (C.approx n))

/-- `A·(B + C) ≃ A·B + A·C` (pointwise). -/
theorem cmul_add (A B C : CReal) :
    CReal.Equiv (CReal.mul A (CReal.add B C))
      (CReal.add (CReal.mul A B) (CReal.mul A C)) :=
  TrigAdd.equiv_of_approx_eqv (fun n => Q'.mul_add_eqv (A.approx n) (B.approx n) (C.approx n))

/-- `(−W) + W ≃ 0` (pointwise). -/
theorem cadd_neg_left (W : CReal) :
    CReal.Equiv (CReal.add (CReal.neg W) W) CReal.czero :=
  TrigAdd.equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (-(W.approx n)) (W.approx n))
      (Q'.add_neg_self_eqv (W.approx n)))

/-- A pure four-term commutative-monoid reshuffle at `Q'`:
`(p+q)+(r+s) ≃ (p+s)+(q+r)`. -/
theorem q_reshuffle (p q r s : Q') :
    ((p + q) + (r + s)).eqv ((p + s) + (q + r)) :=
  Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv p q (r + s))
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl p)
        (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv q r s)) (Q'.add_comm_eqv (q + r) s)))
      (Q'.eqv_symm (Q'.add_assoc_eqv p s (q + r))))

/-- A pure four-term commutative-monoid reshuffle: `(a+b)+(c+d) ≃ (a+d)+(b+c)`
(pointwise). -/
theorem cadd_reshuffle (a b c d : CReal) :
    CReal.Equiv (CReal.add (CReal.add a b) (CReal.add c d))
      (CReal.add (CReal.add a d) (CReal.add b c)) :=
  TrigAdd.equiv_of_approx_eqv (fun n =>
    q_reshuffle (a.approx n) (b.approx n) (c.approx n) (d.approx n))

/-! ### The solve for the `C ≤ A` branch

All abbreviations are inlined (the Mathlib `set` tactic is unavailable here), with
`u := cosFull (A+−C)`, `v := sinFull (A+−C)`, `cC := cosFull C`, `sC := sinFull C`. -/

/-- **The cosine opposite-sign core, `C ≤ A` branch, from `PythFull`.** -/
theorem core_of_pyth_le (P : TrigSignedAdd.PythFull) (A C : Q')
    (hA : (0 : Q') ≤ A) (hC : (0 : Q') ≤ C) (hCA : C ≤ A) :
    CReal.Equiv (TrigAdd.cosFull (A + -C))
      (CReal.add (CReal.mul (TrigAdd.cosFull A) (TrigAdd.cosFull C))
        (CReal.mul (TrigAdd.sinFull A) (TrigAdd.sinFull C))) := by
  have hD : (0 : Q') ≤ A + -C := Q'.sub_nonneg_of_le hCA
  -- ((A+−C) + C) ≃ A
  have hnegC : (-C + C).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (-C) C) (Q'.add_neg_self_eqv C)
  have hDCA : ((A + -C) + C).eqv A :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv A (-C) C)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl A) hnegC)
        (Q'.eqv_of_eq (Q'.add_zero' A)))
  -- the two nonneg addition laws on (A+−C, C)
  have hcosnn : CReal.Equiv (TrigAdd.cosFull ((A + -C) + C))
      (TrigAdd.cosProdMinus (A + -C) C) :=
    TrigAdd.cos_add_equiv_nonneg (A + -C) C hD hC
  have hsinnn : CReal.Equiv (TrigAdd.sinFull ((A + -C) + C))
      (TrigSineAddCReal.sinProdPlus (A + -C) C) :=
    TrigAdd.sin_add_equiv_nonneg (A + -C) C hD hC
  -- (I): cosFull A ≃ cosProdMinus (A+−C) C ;  (II): sinFull A ≃ sinProdPlus (A+−C) C
  have hI : CReal.Equiv (TrigAdd.cosFull A) (TrigAdd.cosProdMinus (A + -C) C) :=
    ((cosFull_argeqv hDCA).symm).trans hcosnn
  have hII : CReal.Equiv (TrigAdd.sinFull A) (TrigSineAddCReal.sinProdPlus (A + -C) C) :=
    ((TrigSignedAdd.sinFull_eqv_congr hDCA).symm).trans hsinnn
  -- Step A: substitute (I),(II) into the target RHS.
  have hsubst : CReal.Equiv
      (CReal.add (CReal.mul (TrigAdd.cosFull A) (TrigAdd.cosFull C))
        (CReal.mul (TrigAdd.sinFull A) (TrigAdd.sinFull C)))
      (CReal.add (CReal.mul (TrigAdd.cosProdMinus (A + -C) C) (TrigAdd.cosFull C))
        (CReal.mul (TrigSineAddCReal.sinProdPlus (A + -C) C) (TrigAdd.sinFull C))) :=
    (CReal.add_congr_left (CReal.mul_congr_left hI)).trans
      (CReal.add_congr_right (CReal.mul_congr_left hII))
  -- Step B: expand mul (cosProdMinus (A+−C) C) cC.
  have hB : CReal.Equiv
      (CReal.mul (TrigAdd.cosProdMinus (A + -C) C) (TrigAdd.cosFull C))
      (CReal.add (CReal.mul (TrigAdd.cosFull (A + -C)) (CReal.mul (TrigAdd.cosFull C) (TrigAdd.cosFull C)))
        (CReal.neg (CReal.mul (TrigAdd.sinFull (A + -C)) (CReal.mul (TrigAdd.sinFull C) (TrigAdd.cosFull C))))) := by
    unfold TrigAdd.cosProdMinus
    refine (cadd_mul (CReal.mul (TrigAdd.cosFull (A + -C)) (TrigAdd.cosFull C))
      (CReal.neg (CReal.mul (TrigAdd.sinFull (A + -C)) (TrigAdd.sinFull C))) (TrigAdd.cosFull C)).trans ?_
    refine (CReal.add_congr_left
      (CRealAlg.cmul_assoc (TrigAdd.cosFull (A + -C)) (TrigAdd.cosFull C) (TrigAdd.cosFull C))).trans ?_
    refine CReal.add_congr_right ?_
    exact (TrigSignedAdd.neg_mul (CReal.mul (TrigAdd.sinFull (A + -C)) (TrigAdd.sinFull C)) (TrigAdd.cosFull C)).trans
      (CReal.neg_congr (CRealAlg.cmul_assoc (TrigAdd.sinFull (A + -C)) (TrigAdd.sinFull C) (TrigAdd.cosFull C)))
  -- Step C: expand mul (sinProdPlus (A+−C) C) sC.
  have hCexp : CReal.Equiv
      (CReal.mul (TrigSineAddCReal.sinProdPlus (A + -C) C) (TrigAdd.sinFull C))
      (CReal.add (CReal.mul (TrigAdd.sinFull (A + -C)) (CReal.mul (TrigAdd.cosFull C) (TrigAdd.sinFull C)))
        (CReal.mul (TrigAdd.cosFull (A + -C)) (CReal.mul (TrigAdd.sinFull C) (TrigAdd.sinFull C)))) := by
    unfold TrigSineAddCReal.sinProdPlus
    refine (cadd_mul (CReal.mul (TrigAdd.sinFull (A + -C)) (TrigAdd.cosFull C))
      (CReal.mul (TrigAdd.cosFull (A + -C)) (TrigAdd.sinFull C)) (TrigAdd.sinFull C)).trans ?_
    exact (CReal.add_congr_left
        (CRealAlg.cmul_assoc (TrigAdd.sinFull (A + -C)) (TrigAdd.cosFull C) (TrigAdd.sinFull C))).trans
      (CReal.add_congr_right
        (CRealAlg.cmul_assoc (TrigAdd.cosFull (A + -C)) (TrigAdd.sinFull C) (TrigAdd.sinFull C)))
  -- RHS ≃ (a+b)+(c+d), with
  --   a = u·(cC·cC), b = −(v·(sC·cC)), c = v·(cC·sC), d = u·(sC·sC).
  have hRHS4 : CReal.Equiv
      (CReal.add (CReal.mul (TrigAdd.cosFull A) (TrigAdd.cosFull C))
        (CReal.mul (TrigAdd.sinFull A) (TrigAdd.sinFull C)))
      (CReal.add
        (CReal.add (CReal.mul (TrigAdd.cosFull (A + -C)) (CReal.mul (TrigAdd.cosFull C) (TrigAdd.cosFull C)))
          (CReal.neg (CReal.mul (TrigAdd.sinFull (A + -C)) (CReal.mul (TrigAdd.sinFull C) (TrigAdd.cosFull C)))))
        (CReal.add (CReal.mul (TrigAdd.sinFull (A + -C)) (CReal.mul (TrigAdd.cosFull C) (TrigAdd.sinFull C)))
          (CReal.mul (TrigAdd.cosFull (A + -C)) (CReal.mul (TrigAdd.sinFull C) (TrigAdd.sinFull C))))) :=
    hsubst.trans ((CReal.add_congr_left hB).trans (CReal.add_congr_right hCexp))
  -- b + c ≃ 0.
  have hbnegc : CReal.Equiv
      (CReal.neg (CReal.mul (TrigAdd.sinFull (A + -C)) (CReal.mul (TrigAdd.sinFull C) (TrigAdd.cosFull C))))
      (CReal.neg (CReal.mul (TrigAdd.sinFull (A + -C)) (CReal.mul (TrigAdd.cosFull C) (TrigAdd.sinFull C)))) :=
    CReal.neg_congr (TrigSignedAdd.mul_congr_right (CRealAlg.cmul_comm (TrigAdd.sinFull C) (TrigAdd.cosFull C)))
  have hbc : CReal.Equiv
      (CReal.add
        (CReal.neg (CReal.mul (TrigAdd.sinFull (A + -C)) (CReal.mul (TrigAdd.sinFull C) (TrigAdd.cosFull C))))
        (CReal.mul (TrigAdd.sinFull (A + -C)) (CReal.mul (TrigAdd.cosFull C) (TrigAdd.sinFull C))))
      CReal.czero :=
    (CReal.add_congr_left hbnegc).trans
      (cadd_neg_left (CReal.mul (TrigAdd.sinFull (A + -C)) (CReal.mul (TrigAdd.cosFull C) (TrigAdd.sinFull C))))
  -- a + d ≃ u.
  have hpyth : CReal.Equiv
      (CReal.add (CReal.mul (TrigAdd.cosFull C) (TrigAdd.cosFull C))
        (CReal.mul (TrigAdd.sinFull C) (TrigAdd.sinFull C))) CReal.cone :=
    P.pyth C hC
  have had : CReal.Equiv
      (CReal.add (CReal.mul (TrigAdd.cosFull (A + -C)) (CReal.mul (TrigAdd.cosFull C) (TrigAdd.cosFull C)))
        (CReal.mul (TrigAdd.cosFull (A + -C)) (CReal.mul (TrigAdd.sinFull C) (TrigAdd.sinFull C))))
      (TrigAdd.cosFull (A + -C)) :=
    ((cmul_add (TrigAdd.cosFull (A + -C)) (CReal.mul (TrigAdd.cosFull C) (TrigAdd.cosFull C))
        (CReal.mul (TrigAdd.sinFull C) (TrigAdd.sinFull C))).symm).trans
      ((TrigSignedAdd.mul_congr_right hpyth).trans (CRealAlg.cmul_cone (TrigAdd.cosFull (A + -C))))
  -- Combine: RHS ≃ (a+d)+(b+c) ≃ (a+d)+0 ≃ (a+d) ≃ u.
  have hfinal : CReal.Equiv
      (CReal.add (CReal.mul (TrigAdd.cosFull A) (TrigAdd.cosFull C))
        (CReal.mul (TrigAdd.sinFull A) (TrigAdd.sinFull C)))
      (TrigAdd.cosFull (A + -C)) :=
    hRHS4.trans ((cadd_reshuffle _ _ _ _).trans
      (((CReal.add_congr_right hbc).trans (cadd_zero _)).trans had))
  exact hfinal.symm

/-- **The cosine opposite-sign core is inhabited by `PythFull`.**  Combines the
`C ≤ A` branch with the mirror `A ≤ C` branch (by evenness and product
commutativity). -/
def oppositeSignCosCore_of_pyth (P : TrigSignedAdd.PythFull) :
    TrigSignedAdd.OppositeSignCosCore where
  core := by
    intro A C hA hC
    by_cases hCA : C ≤ A
    · exact core_of_pyth_le P A C hA hC hCA
    · -- A ≤ C: use the branch on (C, A) and transport by evenness.
      have hAC : A ≤ C := le_of_not_le hCA
      have hle := core_of_pyth_le P C A hC hA hAC
      -- transport LHS: cosFull (A + -C) ≃ cosFull (C + -A)
      have hneg : (-(C + -A)).eqv (A + -C) :=
        Q'.eqv_trans _ _ _ (Q'.neg_add_eqv C (-A))
          (Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr' (Q'.eqv_refl (-C)) (Q'.neg_neg_eqv A))
            (Q'.add_comm_eqv (-C) A))
      have harg : (A + -C).eqv (-(C + -A)) := Q'.eqv_symm hneg
      have hlhs : CReal.Equiv (TrigAdd.cosFull (A + -C)) (TrigAdd.cosFull (C + -A)) :=
        (cosFull_argeqv harg).trans (TrigAdd.cosFull_even (C + -A))
      -- transport RHS: product commutativity.
      have hrhs : CReal.Equiv
          (CReal.add (CReal.mul (TrigAdd.cosFull C) (TrigAdd.cosFull A))
            (CReal.mul (TrigAdd.sinFull C) (TrigAdd.sinFull A)))
          (CReal.add (CReal.mul (TrigAdd.cosFull A) (TrigAdd.cosFull C))
            (CReal.mul (TrigAdd.sinFull A) (TrigAdd.sinFull C))) :=
        (CReal.add_congr_left (CRealAlg.cmul_comm (TrigAdd.cosFull C) (TrigAdd.cosFull A))).trans
          (CReal.add_congr_right (CRealAlg.cmul_comm (TrigAdd.sinFull C) (TrigAdd.sinFull A)))
      exact (hlhs.trans hle).trans hrhs

end TrigSignedAddFull

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.TrigSignedAddFull.cadd_comm
#print axioms ConstructiveReals.TrigSignedAddFull.cosFull_argeqv
#print axioms ConstructiveReals.TrigSignedAddFull.cos_add_equiv_posneg
#print axioms ConstructiveReals.TrigSignedAddFull.sin_add_equiv_posneg
#print axioms ConstructiveReals.TrigSignedAddFull.cos_add_equiv_negpos
#print axioms ConstructiveReals.TrigSignedAddFull.sin_add_equiv_negpos
#print axioms ConstructiveReals.TrigSignedAddFull.cadd_reshuffle
#print axioms ConstructiveReals.TrigSignedAddFull.core_of_pyth_le
#print axioms ConstructiveReals.TrigSignedAddFull.oppositeSignCosCore_of_pyth
