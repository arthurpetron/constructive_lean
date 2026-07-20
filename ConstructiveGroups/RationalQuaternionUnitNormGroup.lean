/-
Constructive group laws for rational unit quaternions.

# Scope

This leaf closes the raw Hamilton algebra from
`RationalQuaternionAlgebra.lean` under its semantic coordinate equality.  The
polynomial identities are certified by the constructive reflected
`RingNormaliser`; no field structure, quotient, or external ring tactic is
used.  It proves the raw laws needed by inversion and packages the unit-norm
subtype as a `ConstructiveGroup`.

# Boundary

The resulting carrier is the group of rational points on the unit
three-sphere.  It is not asserted to be compact, complete, topological, a Lie
group, or all of SU(2).  Haar integration and compact completion remain
separate constructions.

# Constructivity

All operations return explicit representatives and all laws hold relative to
the existing coordinatewise semantic setoid.  There is no choice,
`noncomputable`, `sorry`, `admit`, or new axiom.
-/

import ConstructiveGroups.RationalQuaternionAlgebra
import ConstructiveGroups.ConstructiveGroup
import ConstructiveReals.RingNormaliser

namespace ConstructiveGroups

open ConstructiveReals

namespace RationalQuaternion

local infix:50 " ≈ " => Q'.eqv

/-! ## Reflected Hamilton-polynomial certificates -/

private abbrev PE := ConstructiveReals.RingNormaliser.PolyExpr

/-- Four polynomial expressions, used only to reflect the four Hamilton
coordinates into the constructive ring normaliser. -/
private structure QuaternionExpr where
  r : PE
  i : PE
  j : PE
  k : PE

private def quaternionVar (base : Nat) : QuaternionExpr :=
  ⟨.var base, .var (base + 1), .var (base + 2), .var (base + 3)⟩

private def quaternionScalar (a : PE) : QuaternionExpr :=
  ⟨a, .const 0, .const 0, .const 0⟩

private def quaternionOne : QuaternionExpr :=
  quaternionScalar (.const 1)

private def quaternionConj (x : QuaternionExpr) : QuaternionExpr :=
  ⟨x.r, .neg x.i, .neg x.j, .neg x.k⟩

private def quaternionMul (x y : QuaternionExpr) : QuaternionExpr :=
  ⟨.add
      (.add (.mul x.r y.r) (.neg (.mul x.i y.i)))
      (.add (.neg (.mul x.j y.j)) (.neg (.mul x.k y.k))),
    .add
      (.add (.mul x.r y.i) (.mul x.i y.r))
      (.add (.mul x.j y.k) (.neg (.mul x.k y.j))),
    .add
      (.add (.mul x.r y.j) (.neg (.mul x.i y.k)))
      (.add (.mul x.j y.r) (.mul x.k y.i)),
    .add
      (.add (.mul x.r y.k) (.mul x.i y.j))
      (.add (.neg (.mul x.j y.i)) (.mul x.k y.r))⟩

private def quaternionNormSq (x : QuaternionExpr) : PE :=
  .add
    (.add (.mul x.r x.r) (.mul x.i x.i))
    (.add (.mul x.j x.j) (.mul x.k x.k))

private def evalQuaternionExpr (rho : Nat → Q')
    (x : QuaternionExpr) : RationalQuaternion :=
  ⟨ConstructiveReals.RingNormaliser.eval rho x.r,
    ConstructiveReals.RingNormaliser.eval rho x.i,
    ConstructiveReals.RingNormaliser.eval rho x.j,
    ConstructiveReals.RingNormaliser.eval rho x.k⟩

private theorem evalQuaternionExpr_one (rho : Nat → Q') :
    evalQuaternionExpr rho quaternionOne = one := rfl

private theorem evalQuaternionExpr_conj (rho : Nat → Q')
    (x : QuaternionExpr) :
    evalQuaternionExpr rho (quaternionConj x) =
      conj (evalQuaternionExpr rho x) := rfl

private theorem evalQuaternionExpr_mul (rho : Nat → Q')
    (x y : QuaternionExpr) :
    evalQuaternionExpr rho (quaternionMul x y) =
      mul (evalQuaternionExpr rho x) (evalQuaternionExpr rho y) := rfl

private theorem evalQuaternionExpr_scalar (rho : Nat → Q') (a : PE) :
    evalQuaternionExpr rho (quaternionScalar a) =
      scalar (ConstructiveReals.RingNormaliser.eval rho a) := rfl

private theorem evalQuaternionExpr_normSq (rho : Nat → Q')
    (x : QuaternionExpr) :
    ConstructiveReals.RingNormaliser.eval rho (quaternionNormSq x) =
      normSq (evalQuaternionExpr rho x) := rfl

private theorem evalPolyExpr_mul (rho : Nat → Q') (a b : PE) :
    ConstructiveReals.RingNormaliser.eval rho (.mul a b) =
      ConstructiveReals.RingNormaliser.eval rho a *
        ConstructiveReals.RingNormaliser.eval rho b := rfl

/-- Coordinatewise equality of normal forms. -/
private def NormalEquivalent (x y : QuaternionExpr) : Prop :=
  ConstructiveReals.RingNormaliser.normalize x.r =
      ConstructiveReals.RingNormaliser.normalize y.r ∧
    ConstructiveReals.RingNormaliser.normalize x.i =
      ConstructiveReals.RingNormaliser.normalize y.i ∧
    ConstructiveReals.RingNormaliser.normalize x.j =
      ConstructiveReals.RingNormaliser.normalize y.j ∧
    ConstructiveReals.RingNormaliser.normalize x.k =
      ConstructiveReals.RingNormaliser.normalize y.k

private theorem evalQuaternionExpr_equivalent_of_normal
    (rho : Nat → Q') (x y : QuaternionExpr)
    (h : NormalEquivalent x y) :
    (evalQuaternionExpr rho x).Equivalent (evalQuaternionExpr rho y) :=
  ⟨ConstructiveReals.RingNormaliser.poly_identity_of_normal_eq
      x.r y.r h.1 rho,
    ConstructiveReals.RingNormaliser.poly_identity_of_normal_eq
      x.i y.i h.2.1 rho,
    ConstructiveReals.RingNormaliser.poly_identity_of_normal_eq
      x.j y.j h.2.2.1 rho,
    ConstructiveReals.RingNormaliser.poly_identity_of_normal_eq
      x.k y.k h.2.2.2 rho⟩

private def qx : QuaternionExpr := quaternionVar 0
private def qy : QuaternionExpr := quaternionVar 4
private def qz : QuaternionExpr := quaternionVar 8

private def xyzEnvironment (x y z : RationalQuaternion) : Nat → Q'
  | 0 => x.r
  | 1 => x.i
  | 2 => x.j
  | 3 => x.k
  | 4 => y.r
  | 5 => y.i
  | 6 => y.j
  | 7 => y.k
  | 8 => z.r
  | 9 => z.i
  | 10 => z.j
  | 11 => z.k
  | _ => 0

private theorem eval_qx (x y z : RationalQuaternion) :
    evalQuaternionExpr (xyzEnvironment x y z) qx = x := rfl

private theorem eval_qy (x y z : RationalQuaternion) :
    evalQuaternionExpr (xyzEnvironment x y z) qy = y := rfl

private theorem eval_qz (x y z : RationalQuaternion) :
    evalQuaternionExpr (xyzEnvironment x y z) qz = z := rfl

private theorem quaternionMul_assoc_normal :
    NormalEquivalent (quaternionMul (quaternionMul qx qy) qz)
      (quaternionMul qx (quaternionMul qy qz)) := by
  unfold NormalEquivalent
  decide

private theorem quaternionOne_mul_normal :
    NormalEquivalent (quaternionMul quaternionOne qx) qx := by
  unfold NormalEquivalent
  decide

private theorem quaternionMul_one_normal :
    NormalEquivalent (quaternionMul qx quaternionOne) qx := by
  unfold NormalEquivalent
  decide

private theorem quaternionConj_conj_normal :
    NormalEquivalent (quaternionConj (quaternionConj qx)) qx := by
  unfold NormalEquivalent
  decide

private theorem quaternionConj_one_normal :
    NormalEquivalent (quaternionConj quaternionOne) quaternionOne := by
  unfold NormalEquivalent
  decide

private theorem quaternionConj_mul_normal :
    NormalEquivalent (quaternionConj (quaternionMul qx qy))
      (quaternionMul (quaternionConj qy) (quaternionConj qx)) := by
  unfold NormalEquivalent
  decide

private theorem quaternionMul_conj_self_normal :
    NormalEquivalent (quaternionMul qx (quaternionConj qx))
      (quaternionScalar (quaternionNormSq qx)) := by
  unfold NormalEquivalent
  decide

private theorem quaternionConj_mul_self_normal :
    NormalEquivalent (quaternionMul (quaternionConj qx) qx)
      (quaternionScalar (quaternionNormSq qx)) := by
  unfold NormalEquivalent
  decide

private theorem quaternionNormSq_conj_normal :
    ConstructiveReals.RingNormaliser.normalize
        (quaternionNormSq (quaternionConj qx)) =
      ConstructiveReals.RingNormaliser.normalize (quaternionNormSq qx) := by decide

private theorem quaternionNormSq_mul_normal :
    ConstructiveReals.RingNormaliser.normalize
        (quaternionNormSq (quaternionMul qx qy)) =
      ConstructiveReals.RingNormaliser.normalize
        (.mul (quaternionNormSq qx) (quaternionNormSq qy)) := by decide

/-! ## Raw semantic Hamilton laws -/

/-- Hamilton multiplication is associative up to coordinatewise rational
semantic equality. -/
theorem mul_assoc (x y z : RationalQuaternion) :
    (mul (mul x y) z).Equivalent (mul x (mul y z)) := by
  have h := evalQuaternionExpr_equivalent_of_normal
    (xyzEnvironment x y z)
    (quaternionMul (quaternionMul qx qy) qz)
    (quaternionMul qx (quaternionMul qy qz))
    quaternionMul_assoc_normal
  simpa only [evalQuaternionExpr_mul, eval_qx, eval_qy, eval_qz] using h

/-- The scalar quaternion `1` is a left identity up to semantic equality. -/
theorem one_mul (x : RationalQuaternion) :
    (mul one x).Equivalent x := by
  have h := evalQuaternionExpr_equivalent_of_normal
    (xyzEnvironment x x x) (quaternionMul quaternionOne qx) qx
    quaternionOne_mul_normal
  simpa only [evalQuaternionExpr_mul, evalQuaternionExpr_one, eval_qx] using h

/-- The scalar quaternion `1` is a right identity up to semantic equality. -/
theorem mul_one (x : RationalQuaternion) :
    (mul x one).Equivalent x := by
  have h := evalQuaternionExpr_equivalent_of_normal
    (xyzEnvironment x x x) (quaternionMul qx quaternionOne) qx
    quaternionMul_one_normal
  simpa only [evalQuaternionExpr_mul, evalQuaternionExpr_one, eval_qx] using h

/-- Quaternion conjugation is involutive up to semantic equality. -/
theorem conj_conj (x : RationalQuaternion) :
    (conj (conj x)).Equivalent x := by
  have h := evalQuaternionExpr_equivalent_of_normal
    (xyzEnvironment x x x) (quaternionConj (quaternionConj qx)) qx
    quaternionConj_conj_normal
  simpa only [evalQuaternionExpr_conj, eval_qx] using h

/-- Quaternion conjugation fixes the scalar identity. -/
theorem conj_one : (conj one).Equivalent one := by
  have h := evalQuaternionExpr_equivalent_of_normal
    (xyzEnvironment zero zero zero)
    (quaternionConj quaternionOne) quaternionOne
    quaternionConj_one_normal
  simpa only [evalQuaternionExpr_conj, evalQuaternionExpr_one] using h

/-- Conjugation reverses Hamilton multiplication. -/
theorem conj_mul (x y : RationalQuaternion) :
    (conj (mul x y)).Equivalent (mul (conj y) (conj x)) := by
  have h := evalQuaternionExpr_equivalent_of_normal
    (xyzEnvironment x y x)
    (quaternionConj (quaternionMul qx qy))
    (quaternionMul (quaternionConj qy) (quaternionConj qx))
    quaternionConj_mul_normal
  simpa only [evalQuaternionExpr_conj, evalQuaternionExpr_mul,
    eval_qx, eval_qy] using h

/-- Multiplication by the conjugate on the right gives the scalar squared
norm. -/
theorem mul_conj_self (x : RationalQuaternion) :
    (mul x (conj x)).Equivalent (scalar (normSq x)) := by
  have h := evalQuaternionExpr_equivalent_of_normal
    (xyzEnvironment x x x)
    (quaternionMul qx (quaternionConj qx))
    (quaternionScalar (quaternionNormSq qx))
    quaternionMul_conj_self_normal
  simpa only [evalQuaternionExpr_mul, evalQuaternionExpr_conj,
    evalQuaternionExpr_scalar, evalQuaternionExpr_normSq, eval_qx] using h

/-- Multiplication by the conjugate on the left gives the scalar squared
norm. -/
theorem conj_mul_self (x : RationalQuaternion) :
    (mul (conj x) x).Equivalent (scalar (normSq x)) := by
  have h := evalQuaternionExpr_equivalent_of_normal
    (xyzEnvironment x x x)
    (quaternionMul (quaternionConj qx) qx)
    (quaternionScalar (quaternionNormSq qx))
    quaternionConj_mul_self_normal
  simpa only [evalQuaternionExpr_mul, evalQuaternionExpr_conj,
    evalQuaternionExpr_scalar, evalQuaternionExpr_normSq, eval_qx] using h

/-- Squared norm is preserved by quaternion conjugation. -/
theorem normSq_conj (x : RationalQuaternion) :
    normSq (conj x) ≈ normSq x := by
  have h := ConstructiveReals.RingNormaliser.poly_identity_of_normal_eq
    (quaternionNormSq (quaternionConj qx)) (quaternionNormSq qx)
    quaternionNormSq_conj_normal (xyzEnvironment x x x)
  simpa only [evalQuaternionExpr_normSq, evalQuaternionExpr_conj,
    eval_qx] using h

/-- The four-square identity: Hamilton multiplication multiplies squared
norms. -/
theorem normSq_mul (x y : RationalQuaternion) :
    normSq (mul x y) ≈ normSq x * normSq y := by
  have h := ConstructiveReals.RingNormaliser.poly_identity_of_normal_eq
    (quaternionNormSq (quaternionMul qx qy))
    (.mul (quaternionNormSq qx) (quaternionNormSq qy))
    quaternionNormSq_mul_normal (xyzEnvironment x y x)
  simpa only [evalPolyExpr_mul, evalQuaternionExpr_normSq,
    evalQuaternionExpr_mul, eval_qx, eval_qy] using h

/-- Scalar quaternions respect rational semantic equality. -/
theorem scalar_congr {a b : Q'} (h : a ≈ b) :
    (scalar a).Equivalent (scalar b) :=
  ⟨h, Q'.eqv_refl 0, Q'.eqv_refl 0, Q'.eqv_refl 0⟩

/-! ## The explicit unit-norm operations -/

namespace UnitNorm

/-- Unit-norm semantic equality inherits the raw quaternion setoid. -/
def semanticSetoid : Setoid UnitNorm where
  r := Equivalent
  iseqv := {
    refl := fun x => RationalQuaternion.semanticSetoid.iseqv.refl x.val
    symm := fun h => RationalQuaternion.semanticSetoid.iseqv.symm h
    trans := fun hxy hyz => RationalQuaternion.semanticSetoid.iseqv.trans hxy hyz
  }

private theorem product_eqv_one {a b : Q'}
    (ha : a ≈ 1) (hb : b ≈ 1) : a * b ≈ 1 := by
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a 1 b ha)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left 1 b 1 hb)
      (Q'.one_mul_eqv 1))

/-- Hamilton multiplication is closed on rational unit quaternions. -/
def mul (x y : UnitNorm) : UnitNorm :=
  ⟨RationalQuaternion.mul x.val y.val, by
    unfold IsUnitNorm
    exact Q'.eqv_trans _ _ _
      (RationalQuaternion.normSq_mul x.val y.val)
      (product_eqv_one x.unitNorm y.unitNorm)⟩

/-- Quaternion conjugation is closed on rational unit quaternions. -/
def conj (x : UnitNorm) : UnitNorm :=
  ⟨RationalQuaternion.conj x.val, by
    unfold IsUnitNorm
    exact Q'.eqv_trans _ _ _
      (RationalQuaternion.normSq_conj x.val) x.unitNorm⟩

/-- The inverse of a rational unit quaternion is its conjugate. -/
def inv (x : UnitNorm) : UnitNorm := conj x

/-- Unit-norm multiplication respects semantic equality. -/
theorem mul_congr {x x' y y' : UnitNorm}
    (hx : x.Equivalent x') (hy : y.Equivalent y') :
    (mul x y).Equivalent (mul x' y') :=
  RationalQuaternion.mul_congr hx hy

/-- Unit-norm conjugation respects semantic equality. -/
theorem conj_congr {x y : UnitNorm} (h : x.Equivalent y) :
    (conj x).Equivalent (conj y) :=
  RationalQuaternion.conj_congr h

/-- Unit-norm inversion respects semantic equality. -/
theorem inv_congr {x y : UnitNorm} (h : x.Equivalent y) :
    (inv x).Equivalent (inv y) :=
  conj_congr h

/-- Unit-norm multiplication is associative modulo semantic equality. -/
theorem mul_assoc (x y z : UnitNorm) :
    (mul (mul x y) z).Equivalent (mul x (mul y z)) :=
  RationalQuaternion.mul_assoc x.val y.val z.val

/-- The existing explicit `unitOne` is a left identity. -/
theorem one_mul (x : UnitNorm) : (mul unitOne x).Equivalent x :=
  RationalQuaternion.one_mul x.val

/-- The existing explicit `unitOne` is a right identity. -/
theorem mul_one (x : UnitNorm) : (mul x unitOne).Equivalent x :=
  RationalQuaternion.mul_one x.val

/-- Conjugation is involutive on the unit-norm carrier. -/
theorem conj_conj (x : UnitNorm) : (conj (conj x)).Equivalent x :=
  RationalQuaternion.conj_conj x.val

/-- Conjugation reverses unit-norm multiplication. -/
theorem conj_mul (x y : UnitNorm) :
    (conj (mul x y)).Equivalent (mul (conj y) (conj x)) :=
  RationalQuaternion.conj_mul x.val y.val

/-- Conjugation, hence inversion, is a left inverse on unit quaternions. -/
theorem inv_mul (x : UnitNorm) : (mul (inv x) x).Equivalent unitOne := by
  exact RationalQuaternion.semanticSetoid.iseqv.trans
    (RationalQuaternion.conj_mul_self x.val)
    (RationalQuaternion.scalar_congr x.unitNorm)

/-- Conjugation, hence inversion, is a right inverse on unit quaternions. -/
theorem mul_inv (x : UnitNorm) : (mul x (inv x)).Equivalent unitOne := by
  exact RationalQuaternion.semanticSetoid.iseqv.trans
    (RationalQuaternion.mul_conj_self x.val)
    (RationalQuaternion.scalar_congr x.unitNorm)

/-- The rational points of the unit three-sphere form a constructive setoid
group under Hamilton multiplication. -/
def group : ConstructiveGroup where
  Carrier := UnitNorm
  setoid := semanticSetoid
  one := unitOne
  mul := mul
  inv := inv
  mul_congr := mul_congr
  inv_congr := inv_congr
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  inv_mul := inv_mul
  mul_inv := mul_inv

end UnitNorm

end RationalQuaternion

end ConstructiveGroups

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms ConstructiveGroups.RationalQuaternion.mul_assoc
#print axioms ConstructiveGroups.RationalQuaternion.one_mul
#print axioms ConstructiveGroups.RationalQuaternion.mul_one
#print axioms ConstructiveGroups.RationalQuaternion.conj_conj
#print axioms ConstructiveGroups.RationalQuaternion.conj_mul
#print axioms ConstructiveGroups.RationalQuaternion.mul_conj_self
#print axioms ConstructiveGroups.RationalQuaternion.conj_mul_self
#print axioms ConstructiveGroups.RationalQuaternion.normSq_conj
#print axioms ConstructiveGroups.RationalQuaternion.normSq_mul
#print axioms ConstructiveGroups.RationalQuaternion.UnitNorm.mul
#print axioms ConstructiveGroups.RationalQuaternion.UnitNorm.conj
#print axioms ConstructiveGroups.RationalQuaternion.UnitNorm.inv_mul
#print axioms ConstructiveGroups.RationalQuaternion.UnitNorm.mul_inv
#print axioms ConstructiveGroups.RationalQuaternion.UnitNorm.group
