/-
Raw rational quaternion algebra over the constructive rationals `Q'`.

# Scope

This low-level leaf supplies the algebraic rational skeleton needed before any
genuine compact-group realization can be attempted.  Its carrier is raw
`Q'^4`, with coordinatewise semantic equality, Hamilton multiplication,
conjugation, and the squared norm.  It also records the honest semantic
unit-norm carrier.

# Boundary

The full group structure on every rational point of the unit three-sphere
requires the multivariate four-square identity and Hamilton associativity at
`Q'.eqv`.  Those polynomial proofs are deliberately not replaced by fields or
assumptions here.  In particular, this module does not claim a rational
unit-quaternion group, a compact group, SU(2), SO(3), or a topological/Lie-group
realization.

# Constructivity

All data and witnesses are explicit.  This file stays within the project's
constructive rational core and has no continuum or quotient dependency.
-/

import ConstructiveReals.RationalsMul

namespace ConstructiveGroups

open ConstructiveReals

/-! ## Raw rational quaternion coordinates -/

/-- Raw Hamilton coordinates `r + i·I + j·J + k·K` over the constructive
rationals.  No normalization or unit-norm condition is built into this type. -/
structure RationalQuaternion where
  r : Q'
  i : Q'
  j : Q'
  k : Q'
deriving DecidableEq, Repr

namespace RationalQuaternion

/-- Coordinatewise semantic equality of raw rational quaternions. -/
@[inline] def Equivalent (x y : RationalQuaternion) : Prop :=
  x.r.eqv y.r ∧ x.i.eqv y.i ∧ x.j.eqv y.j ∧ x.k.eqv y.k

/-- Coordinatewise semantic equality is decidable by rational
cross-multiplication. -/
def decidableEquivalent (x y : RationalQuaternion) : Decidable (Equivalent x y) :=
  by
    unfold Equivalent Q'.eqv
    infer_instance

/-- The coordinatewise semantic setoid on `Q'^4`. -/
def semanticSetoid : Setoid RationalQuaternion where
  r := Equivalent
  iseqv := {
    refl := fun x =>
      ⟨Q'.eqv_refl x.r, Q'.eqv_refl x.i,
        Q'.eqv_refl x.j, Q'.eqv_refl x.k⟩
    symm := by
      intro x y h
      exact ⟨Q'.eqv_symm h.1, Q'.eqv_symm h.2.1,
        Q'.eqv_symm h.2.2.1, Q'.eqv_symm h.2.2.2⟩
    trans := by
      intro x y z hxy hyz
      exact
        ⟨Q'.eqv_trans x.r y.r z.r hxy.1 hyz.1,
          Q'.eqv_trans x.i y.i z.i hxy.2.1 hyz.2.1,
          Q'.eqv_trans x.j y.j z.j hxy.2.2.1 hyz.2.2.1,
          Q'.eqv_trans x.k y.k z.k hxy.2.2.2 hyz.2.2.2⟩
  }

/-- Scalar quaternion. -/
@[inline] def scalar (a : Q') : RationalQuaternion :=
  ⟨a, 0, 0, 0⟩

/-- Additive zero quaternion. -/
def zero : RationalQuaternion := scalar 0

/-- Multiplicative identity quaternion. -/
def one : RationalQuaternion := scalar 1

/-- The first standard imaginary basis unit. -/
def basisI : RationalQuaternion := ⟨0, 1, 0, 0⟩

/-- The second standard imaginary basis unit. -/
def basisJ : RationalQuaternion := ⟨0, 0, 1, 0⟩

/-- The third standard imaginary basis unit. -/
def basisK : RationalQuaternion := ⟨0, 0, 0, 1⟩

/-- Coordinatewise additive inverse. -/
@[inline] def neg (x : RationalQuaternion) : RationalQuaternion :=
  ⟨-x.r, -x.i, -x.j, -x.k⟩

/-- Quaternion conjugation. -/
@[inline] def conj (x : RationalQuaternion) : RationalQuaternion :=
  ⟨x.r, -x.i, -x.j, -x.k⟩

/-- Hamilton multiplication in scalar-first coordinates. -/
@[inline] def mul (x y : RationalQuaternion) : RationalQuaternion :=
  ⟨((x.r * y.r + -(x.i * y.i)) +
      (-(x.j * y.j) + -(x.k * y.k))),
    ((x.r * y.i + x.i * y.r) +
      (x.j * y.k + -(x.k * y.j))),
    ((x.r * y.j + -(x.i * y.k)) +
      (x.j * y.r + x.k * y.i)),
    ((x.r * y.k + x.i * y.j) +
      (-(x.j * y.i) + x.k * y.r))⟩

/-- Squared Euclidean norm of the four rational coordinates. -/
@[inline] def normSq (x : RationalQuaternion) : Q' :=
  (x.r * x.r + x.i * x.i) + (x.j * x.j + x.k * x.k)

/-- Honest semantic unit-norm condition. -/
@[inline] def IsUnitNorm (x : RationalQuaternion) : Prop :=
  (normSq x).eqv 1

/-- Raw rational unit-quaternion carrier.  Operations on this carrier are
added only after their polynomial closure laws have been proved. -/
structure UnitNorm where
  val : RationalQuaternion
  unitNorm : IsUnitNorm val

/-- Unit-norm representatives inherit coordinatewise semantic equality. -/
@[inline] def UnitNorm.Equivalent (x y : UnitNorm) : Prop :=
  x.val.Equivalent y.val

/-- Unit-norm semantic equality is decidable from the four rational
cross-products; the proof fields are irrelevant. -/
def UnitNorm.decidableEquivalent (x y : UnitNorm) :
    Decidable (x.Equivalent y) :=
  RationalQuaternion.decidableEquivalent x.val y.val

/-- The scalar identity has unit norm. -/
def unitOne : UnitNorm :=
  ⟨one, by
    unfold IsUnitNorm normSq one scalar
    decide⟩

/-- The negative scalar identity has unit norm. -/
def unitNegativeOne : UnitNorm :=
  ⟨neg one, by
    unfold IsUnitNorm normSq neg one scalar
    decide⟩

/-! ## Semantic congruence of the raw operations -/

private theorem qMulCongr {a a' b b' : Q'}
    (ha : a.eqv a') (hb : b.eqv b') :
    (a * b).eqv (a' * b') :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

private theorem qAddCongr {a a' b b' : Q'}
    (ha : a.eqv a') (hb : b.eqv b') :
    (a + b).eqv (a' + b') :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right a a' b ha)
    (Q'.add_eqv_congr_left a' b b' hb)

private theorem qNegCongr {a b : Q'} (h : a.eqv b) :
    (-a).eqv (-b) :=
  Q'.neg_eqv_congr a b h

/-- Coordinatewise negation respects rational semantic equality. -/
theorem neg_congr {x y : RationalQuaternion} (h : x.Equivalent y) :
    (neg x).Equivalent (neg y) :=
  ⟨qNegCongr h.1, qNegCongr h.2.1,
    qNegCongr h.2.2.1, qNegCongr h.2.2.2⟩

/-- Quaternion conjugation respects rational semantic equality. -/
theorem conj_congr {x y : RationalQuaternion} (h : x.Equivalent y) :
    (conj x).Equivalent (conj y) :=
  ⟨h.1, qNegCongr h.2.1,
    qNegCongr h.2.2.1, qNegCongr h.2.2.2⟩

/-- Hamilton multiplication respects coordinatewise semantic equality. -/
theorem mul_congr {x x' y y' : RationalQuaternion}
    (hx : x.Equivalent x') (hy : y.Equivalent y') :
    (mul x y).Equivalent (mul x' y') := by
  exact
    ⟨qAddCongr
        (qAddCongr
          (qMulCongr hx.1 hy.1)
          (qNegCongr (qMulCongr hx.2.1 hy.2.1)))
        (qAddCongr
          (qNegCongr (qMulCongr hx.2.2.1 hy.2.2.1))
          (qNegCongr (qMulCongr hx.2.2.2 hy.2.2.2))),
      qAddCongr
        (qAddCongr
          (qMulCongr hx.1 hy.2.1)
          (qMulCongr hx.2.1 hy.1))
        (qAddCongr
          (qMulCongr hx.2.2.1 hy.2.2.2)
          (qNegCongr (qMulCongr hx.2.2.2 hy.2.2.1))),
      qAddCongr
        (qAddCongr
          (qMulCongr hx.1 hy.2.2.1)
          (qNegCongr (qMulCongr hx.2.1 hy.2.2.2)))
        (qAddCongr
          (qMulCongr hx.2.2.1 hy.1)
          (qMulCongr hx.2.2.2 hy.2.1)),
      qAddCongr
        (qAddCongr
          (qMulCongr hx.1 hy.2.2.2)
          (qMulCongr hx.2.1 hy.2.2.1))
        (qAddCongr
          (qNegCongr (qMulCongr hx.2.2.1 hy.2.1))
          (qMulCongr hx.2.2.2 hy.1))⟩

/-- Squared norm respects coordinatewise semantic equality. -/
theorem normSq_congr {x y : RationalQuaternion} (h : x.Equivalent y) :
    (normSq x).eqv (normSq y) :=
  qAddCongr
    (qAddCongr (qMulCongr h.1 h.1) (qMulCongr h.2.1 h.2.1))
    (qAddCongr (qMulCongr h.2.2.1 h.2.2.1)
      (qMulCongr h.2.2.2 h.2.2.2))

end RationalQuaternion

end ConstructiveGroups

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms ConstructiveGroups.RationalQuaternion.semanticSetoid
#print axioms ConstructiveGroups.RationalQuaternion.neg_congr
#print axioms ConstructiveGroups.RationalQuaternion.conj_congr
#print axioms ConstructiveGroups.RationalQuaternion.mul_congr
#print axioms ConstructiveGroups.RationalQuaternion.normSq_congr
