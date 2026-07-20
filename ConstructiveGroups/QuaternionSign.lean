/-
The complete two-element sign group.

This leaf presents the scalar signs independently of any ambient quaternion
group.  It is reusable by both finite verification fixtures and the eventual
full rational unit-quaternion construction.
-/

import ConstructiveGroups.ConstructiveGroup

namespace ConstructiveGroups

/-- The two scalar signs, written independently of any ambient quaternion
group. -/
inductive QuaternionSign where
  | positive
  | negative
deriving DecidableEq, Repr

namespace QuaternionSign

/-- Multiplication of scalar signs. -/
@[inline] def mul : QuaternionSign → QuaternionSign → QuaternionSign
  | .positive, z => z
  | .negative, .positive => .negative
  | .negative, .negative => .positive

/-- Both scalar signs are self-inverse. -/
@[inline] def inv (z : QuaternionSign) : QuaternionSign := z

/-- Equality setoid for the two-element sign carrier. -/
def equalitySetoid : Setoid QuaternionSign where
  r := Eq
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂
  }

/-- Constructive group presentation of the two scalar signs. -/
def group : ConstructiveGroup where
  Carrier := QuaternionSign
  setoid := equalitySetoid
  one := .positive
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
  mul_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> rfl
  one_mul := by
    intro a
    cases a <;> rfl
  mul_one := by
    intro a
    cases a <;> rfl
  inv_mul := by
    intro a
    cases a <;> rfl
  mul_inv := by
    intro a
    cases a <;> rfl

/-- Explicit duplicate-free enumeration of both scalar signs. -/
def finite : FiniteGroupPresentation group where
  size := 2
  enumerate := fun index =>
    Fin.cases .positive (fun _ => .negative) index
  cover := by
    intro z
    cases z
    · refine ⟨⟨0, by decide⟩, ?_⟩
      change QuaternionSign.positive = QuaternionSign.positive
      rfl
    · refine ⟨⟨1, by decide⟩, ?_⟩
      change QuaternionSign.negative = QuaternionSign.negative
      rfl

end QuaternionSign

end ConstructiveGroups

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms ConstructiveGroups.QuaternionSign.group
#print axioms ConstructiveGroups.QuaternionSign.finite
