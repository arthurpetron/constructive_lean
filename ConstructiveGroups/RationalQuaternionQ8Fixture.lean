/-
Finite rational quaternion Q8 fixture.

# Scope

This leaf supplies a completely explicit finite verification fixture: the
eight signed coordinate-basis units form the rational quaternion group Q8,
the two scalar signs form its finite central subgroup, and the imported
located-coset construction produces their exact setoid quotient.  Its
coordinate realization uses the independent raw rational quaternion algebra.

# Boundary

The eight-element fixture realizes the Q8 multiplication table as eight
rational unit-norm quaternion points.  This file does not construct the
ambient group of all rational unit quaternions or prove that the finite code is
a subgroup of such an ambient object.  It is not a compact group, SU(2),
SO(3), or a topological/Lie-group realization.  In particular, this finite
validation fixture does not complete the rational A1 construction.

# Constructivity

All witnesses are explicit data.  The only semantic truncation is the one
internal to the imported located-coset relation.  This file stays within the
project's constructive core and has no continuum dependency.
-/

import ConstructiveGroups.RationalQuaternionAlgebra
import ConstructiveGroups.QuaternionSign
import ConstructiveGroups.LocatedCentralQuotient

namespace ConstructiveGroups

open ConstructiveReals

/-! ## Eight signed rational basis units -/

/-- The four unsigned quaternion basis axes. -/
inductive QuaternionBasisAxis where
  | one
  | i
  | j
  | k
deriving DecidableEq, Repr

/-- A sign and basis axis encode one of `±1, ±I, ±J, ±K`. -/
structure RationalQuaternionBasisUnit where
  negative : Bool
  axis : QuaternionBasisAxis
deriving DecidableEq, Repr

namespace RationalQuaternionBasisUnit

/-- Canonical signed-axis constructor. -/
@[inline] def make (negative : Bool) (axis : QuaternionBasisAxis) :
    RationalQuaternionBasisUnit :=
  ⟨negative, axis⟩

/-- Multiplication table of the four unsigned axes, including the sign
created by `I² = J² = K² = IJK = -1`. -/
def axisMul : QuaternionBasisAxis → QuaternionBasisAxis →
    RationalQuaternionBasisUnit
  | .one, b => make false b
  | a, .one => make false a
  | .i, .i => make true .one
  | .j, .j => make true .one
  | .k, .k => make true .one
  | .i, .j => make false .k
  | .j, .k => make false .i
  | .k, .i => make false .j
  | .j, .i => make true .k
  | .k, .j => make true .i
  | .i, .k => make true .j

/-- Quaternion-basis multiplication.  Scalar signs combine by exclusive-or
with the sign from the unsigned-axis table. -/
@[inline] def mul (x y : RationalQuaternionBasisUnit) :
    RationalQuaternionBasisUnit :=
  let base := axisMul x.axis y.axis
  make (Bool.xor (Bool.xor x.negative y.negative) base.negative) base.axis

/-- Inversion of a signed basis unit.  Scalar units are self-inverse;
imaginary axes acquire the opposite sign. -/
@[inline] def inv (x : RationalQuaternionBasisUnit) :
    RationalQuaternionBasisUnit :=
  match x.axis with
  | .one => x
  | axis => make (!x.negative) axis

/-- Positive scalar basis unit. -/
def one : RationalQuaternionBasisUnit := make false .one

/-- Negative scalar basis unit. -/
def negativeOne : RationalQuaternionBasisUnit := make true .one

/-- Realization of a basis code in raw rational Hamilton coordinates. -/
def toQuaternion (x : RationalQuaternionBasisUnit) : RationalQuaternion :=
  let unsigned :=
    match x.axis with
    | .one => RationalQuaternion.one
    | .i => RationalQuaternion.basisI
    | .j => RationalQuaternion.basisJ
    | .k => RationalQuaternion.basisK
  match x.negative with
  | false => unsigned
  | true => RationalQuaternion.neg unsigned

/-- Every signed basis unit has rational squared norm one. -/
theorem toQuaternion_unitNorm (x : RationalQuaternionBasisUnit) :
    RationalQuaternion.IsUnitNorm x.toQuaternion := by
  rcases x with ⟨negative, axis⟩
  cases negative <;> cases axis <;>
    unfold RationalQuaternion.IsUnitNorm RationalQuaternion.normSq Q'.eqv <;>
    decide

/-- The coordinate realization reflects semantic equality: the eight signed
basis codes denote eight distinct rational quaternions. -/
theorem toQuaternion_reflectsEquivalent
    (x y : RationalQuaternionBasisUnit) :
    RationalQuaternion.Equivalent (toQuaternion x) (toQuaternion y) →
      x = y := by
  rcases x with ⟨sx, ax⟩
  rcases y with ⟨sy, ay⟩
  cases sx <;> cases ax <;> cases sy <;> cases ay <;>
    unfold RationalQuaternion.Equivalent Q'.eqv <;> decide

/-- Signed-axis multiplication realizes the Hamilton multiplication table. -/
theorem toQuaternion_mul (x y : RationalQuaternionBasisUnit) :
    RationalQuaternion.Equivalent (toQuaternion (mul x y))
      (RationalQuaternion.mul (toQuaternion x) (toQuaternion y)) := by
  rcases x with ⟨sx, ax⟩
  rcases y with ⟨sy, ay⟩
  cases sx <;> cases ax <;> cases sy <;> cases ay <;>
    unfold RationalQuaternion.Equivalent Q'.eqv <;> decide

/-- Equality setoid on the finite code carrier. -/
def equalitySetoid : Setoid RationalQuaternionBasisUnit where
  r := Eq
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂
  }

/-- Associativity of the signed quaternion-basis table. -/
theorem mul_assoc (x y z : RationalQuaternionBasisUnit) :
    mul (mul x y) z = mul x (mul y z) := by
  rcases x with ⟨sx, ax⟩
  rcases y with ⟨sy, ay⟩
  rcases z with ⟨sz, az⟩
  cases sx <;> cases ax <;>
    cases sy <;> cases ay <;>
    cases sz <;> cases az <;> decide

/-- The positive scalar code is a left identity. -/
theorem one_mul (x : RationalQuaternionBasisUnit) : mul one x = x := by
  rcases x with ⟨sx, ax⟩
  cases sx <;> cases ax <;> decide

/-- The positive scalar code is a right identity. -/
theorem mul_one (x : RationalQuaternionBasisUnit) : mul x one = x := by
  rcases x with ⟨sx, ax⟩
  cases sx <;> cases ax <;> decide

/-- The table inverse is a left inverse. -/
theorem inv_mul (x : RationalQuaternionBasisUnit) : mul (inv x) x = one := by
  rcases x with ⟨sx, ax⟩
  cases sx <;> cases ax <;> decide

/-- The table inverse is a right inverse. -/
theorem mul_inv (x : RationalQuaternionBasisUnit) : mul x (inv x) = one := by
  rcases x with ⟨sx, ax⟩
  cases sx <;> cases ax <;> decide

/-- Constructive group of the eight signed rational basis units. -/
def group : ConstructiveGroup where
  Carrier := RationalQuaternionBasisUnit
  setoid := equalitySetoid
  one := one
  mul := mul
  inv := inv
  mul_congr := by
    intro a a' b b' ha hb
    cases ha
    cases hb
    rfl
  inv_congr := by
    intro a b h
    cases h
    rfl
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  inv_mul := inv_mul
  mul_inv := mul_inv

/-! ## The two scalar signs as an explicit finite central subgroup -/

/-- Inclusion of the two scalar signs into the eight basis units. -/
def includeSign : QuaternionSign → RationalQuaternionBasisUnit
  | .positive => one
  | .negative => negativeOne

/-- The scalar-sign inclusion is a constructive group homomorphism. -/
def signInclusion : ConstructiveGroup.Hom QuaternionSign.group group where
  toFun := includeSign
  map_equivalent := by
    intro x y h
    cases h
    rfl
  map_one := rfl
  map_mul := by
    intro x y
    cases x <;> cases y <;> change _ = _ <;> decide

/-- Included scalar signs commute with all eight rational basis units. -/
theorem includeSign_central (z : QuaternionSign)
    (x : RationalQuaternionBasisUnit) :
    mul (includeSign z) x = mul x (includeSign z) := by
  cases z
  · exact (one_mul x).trans (mul_one x).symm
  · rcases x with ⟨sx, ax⟩
    cases sx <;> cases ax <;> decide

/-- The two scalar signs form an explicit finite central subgroup of the
eight-element rational unit-basis fixture. -/
def signCentralSubgroup : FiniteCentralSubgroup group where
  group := QuaternionSign.group
  finite := QuaternionSign.finite
  inclusion := signInclusion
  injective := by
    intro z w h
    change includeSign z = includeSign w at h
    change z = w
    cases z <;> cases w <;> simp_all [includeSign, one, negativeOne, make]
  central := includeSign_central

/-- Decidable ambient semantic equality used by the finite locator. -/
def decidableEquivalent (x y : group.Carrier) :
    Decidable (group.Equivalent x y) :=
  by
    change RationalQuaternionBasisUnit at x
    change RationalQuaternionBasisUnit at y
    change Decidable (x = y)
    infer_instance

/-- Finite search returns a scalar-sign witness relating two basis units, or
constructively refutes every such witness. -/
def signLocator : signCentralSubgroup.Locator :=
  FiniteCentralSubgroup.Locator.ofDecidableEquivalent
    signCentralSubgroup decidableEquivalent

/-- Located setoid quotient of the eight rational basis units by their two
scalar signs.  This is a finite algebraic fixture, not SO(3). -/
def signLocatedQuotientGroup : ConstructiveGroup :=
  FiniteCentralSubgroup.locatedCentralQuotientGroup
    signCentralSubgroup signLocator

/-- Exact central-quotient presentation for the finite basis-unit fixture. -/
def signLocatedQuotientPresentation :
    CentralQuotientPresentation group signLocatedQuotientGroup :=
  FiniteCentralSubgroup.locatedCentralQuotientPresentation
    signCentralSubgroup signLocator

end RationalQuaternionBasisUnit

end ConstructiveGroups

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms ConstructiveGroups.RationalQuaternionBasisUnit.toQuaternion_unitNorm
#print axioms ConstructiveGroups.RationalQuaternionBasisUnit.toQuaternion_reflectsEquivalent
#print axioms ConstructiveGroups.RationalQuaternionBasisUnit.toQuaternion_mul
#print axioms ConstructiveGroups.RationalQuaternionBasisUnit.mul_assoc
#print axioms ConstructiveGroups.RationalQuaternionBasisUnit.one_mul
#print axioms ConstructiveGroups.RationalQuaternionBasisUnit.mul_one
#print axioms ConstructiveGroups.RationalQuaternionBasisUnit.inv_mul
#print axioms ConstructiveGroups.RationalQuaternionBasisUnit.mul_inv
#print axioms ConstructiveGroups.RationalQuaternionBasisUnit.group
#print axioms ConstructiveGroups.RationalQuaternionBasisUnit.signInclusion
#print axioms ConstructiveGroups.RationalQuaternionBasisUnit.includeSign_central
#print axioms ConstructiveGroups.RationalQuaternionBasisUnit.signCentralSubgroup
#print axioms ConstructiveGroups.RationalQuaternionBasisUnit.signLocator
#print axioms ConstructiveGroups.RationalQuaternionBasisUnit.signLocatedQuotientPresentation
