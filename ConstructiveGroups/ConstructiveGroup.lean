/-
Constructive setoid-group and finite-central-quotient presentations.

# Scope

This module is the cycle-free algebraic foundation for the global-form layer of
a compact-group realization program.  It depends only on Lean core and keeps
all equality-sensitive operations relative to an explicitly supplied setoid.
In particular, representative-producing claims return `PSigma` (`Σ'`) data;
no witness is hidden in `Exists` or `Nonempty`.

The hierarchy records:

* a group carried by a setoid, with all laws stated modulo its equivalence;
* homomorphisms that respect the source and target setoids;
* a finite enumeration with constructive coverage;
* an injectively included finite central subgroup; and
* a quotient homomorphism whose surjectivity and exact kernel come with
  explicit representatives and explicit central witnesses.

# Boundary

`CentralQuotientPresentation` is an **algebraic presentation** of a central
quotient.  It does not construct a Lean quotient type, choose canonical
representatives, or assert topology, compactness, a metric, Haar integration,
Lie-group smoothness, simple connectedness, or Lie-algebra simplicity.  Those
are separate higher layers.  Its upstream parameter is therefore called
`coverGroup`, not `simplyConnected`: a later realization must separately prove
that a chosen cover has the required topological property.

# Constructivity

There is no Mathlib import, classical reasoning, choice, `Nonempty`, quotient,
or `noncomputable` declaration in this file.  A finite presentation need not
be duplicate-free: its `size` is the number of enumerating slots, while
`cover` constructively returns a slot representing every element modulo the
setoid.
-/

universe u v w

namespace ConstructiveGroups

/-! ## Setoid groups -/

/-- A constructive group whose equality is an explicitly supplied setoid.

Every algebraic law is stated modulo `setoid.r`.  In particular, the carrier
need not have useful structural equality and no quotient or choice of normal
form is required. -/
structure ConstructiveGroup where
  /-- Raw representatives of group elements. -/
  Carrier : Type u
  /-- Semantic equality of representatives. -/
  setoid : Setoid Carrier
  /-- Identity representative. -/
  one : Carrier
  /-- Multiplication on representatives. -/
  mul : Carrier → Carrier → Carrier
  /-- Inversion on representatives. -/
  inv : Carrier → Carrier
  /-- Multiplication respects semantic equality in both arguments. -/
  mul_congr : ∀ {a a' b b' : Carrier},
    setoid.r a a' → setoid.r b b' →
      setoid.r (mul a b) (mul a' b')
  /-- Inversion respects semantic equality. -/
  inv_congr : ∀ {a b : Carrier},
    setoid.r a b → setoid.r (inv a) (inv b)
  /-- Associativity modulo semantic equality. -/
  mul_assoc : ∀ a b c : Carrier,
    setoid.r (mul (mul a b) c) (mul a (mul b c))
  /-- Left identity modulo semantic equality. -/
  one_mul : ∀ a : Carrier, setoid.r (mul one a) a
  /-- Right identity modulo semantic equality. -/
  mul_one : ∀ a : Carrier, setoid.r (mul a one) a
  /-- Left inverse modulo semantic equality. -/
  inv_mul : ∀ a : Carrier, setoid.r (mul (inv a) a) one
  /-- Right inverse modulo semantic equality. -/
  mul_inv : ∀ a : Carrier, setoid.r (mul a (inv a)) one

/-- Explicit semantic equivalence helper for a `ConstructiveGroup`.

Using a group-indexed helper avoids installing a global `Setoid` instance for
the raw carrier, which could otherwise become ambiguous when the same carrier
is presented by more than one semantic equality. -/
@[inline] def ConstructiveGroup.Equivalent
    (G : ConstructiveGroup.{u}) (x y : G.Carrier) : Prop :=
  G.setoid.r x y

/-- Semantic equivalence is reflexive. -/
theorem ConstructiveGroup.equivalent_refl
    (G : ConstructiveGroup.{u}) (x : G.Carrier) :
    G.Equivalent x x :=
  G.setoid.iseqv.refl x

/-- Semantic equivalence is symmetric. -/
theorem ConstructiveGroup.equivalent_symm
    (G : ConstructiveGroup.{u}) {x y : G.Carrier}
    (h : G.Equivalent x y) :
    G.Equivalent y x :=
  G.setoid.iseqv.symm h

/-- Semantic equivalence is transitive. -/
theorem ConstructiveGroup.equivalent_trans
    (G : ConstructiveGroup.{u}) {x y z : G.Carrier}
    (hxy : G.Equivalent x y) (hyz : G.Equivalent y z) :
    G.Equivalent x z :=
  G.setoid.iseqv.trans hxy hyz

/-! ## Setoid-group homomorphisms -/

namespace ConstructiveGroup

/-- A homomorphism of constructive setoid groups.

The map is a function on representatives together with congruence and the two
primitive homomorphism laws.  Inverse preservation can later be derived from
the group laws; it is deliberately not duplicated as foundational data. -/
structure Hom (source : ConstructiveGroup.{u})
    (target : ConstructiveGroup.{v}) where
  /-- Map on representatives. -/
  toFun : source.Carrier → target.Carrier
  /-- The map respects semantic equality. -/
  map_equivalent : ∀ {x y : source.Carrier},
    source.Equivalent x y →
      target.Equivalent (toFun x) (toFun y)
  /-- The source identity maps to the target identity modulo the setoid. -/
  map_one : target.Equivalent (toFun source.one) target.one
  /-- Multiplication is preserved modulo the target setoid. -/
  map_mul : ∀ x y : source.Carrier,
    target.Equivalent (toFun (source.mul x y))
      (target.mul (toFun x) (toFun y))

end ConstructiveGroup

/-! ## Finite presentations and finite central subgroups -/

/-- A finite enumeration of a constructive group, with coverage as data.

`cover x` computes an index whose enumerated representative is semantically
equivalent to `x`.  Repetitions are allowed, so `size` is an enumeration bound
and is not asserted to be the quotient-set cardinality. -/
structure FiniteGroupPresentation (G : ConstructiveGroup.{u}) where
  /-- Number of slots in the finite enumeration. -/
  size : Nat
  /-- Representative stored in each enumeration slot. -/
  enumerate : Fin size → G.Carrier
  /-- Constructive coverage modulo the group setoid. -/
  cover : (x : G.Carrier) →
    Σ' i : Fin size, G.Equivalent (enumerate i) x

/-- A finite central subgroup presented by an injective homomorphism.

Injectivity is semantic injectivity: equality of included representatives in
the ambient setoid reflects equality in the subgroup setoid.  Centrality is
also stated modulo the ambient setoid. -/
structure FiniteCentralSubgroup
    (ambient : ConstructiveGroup.{u}) where
  /-- The finite group's own constructive setoid-group presentation. -/
  group : ConstructiveGroup.{v}
  /-- A constructive finite enumeration of the subgroup. -/
  finite : FiniteGroupPresentation group
  /-- Inclusion into the ambient group. -/
  inclusion : ConstructiveGroup.Hom group ambient
  /-- The inclusion reflects semantic equality. -/
  injective : ∀ {z w : group.Carrier},
    ambient.Equivalent (inclusion.toFun z) (inclusion.toFun w) →
      group.Equivalent z w
  /-- Every included element commutes with every ambient element. -/
  central : ∀ (z : group.Carrier) (x : ambient.Carrier),
    ambient.Equivalent (ambient.mul (inclusion.toFun z) x)
      (ambient.mul x (inclusion.toFun z))

/-- An explicit witness that `x` is represented by an element of the included
finite central subgroup.

This is a `PSigma`, not a propositionally truncated existential: downstream
code can project and compute with the central representative `z`. -/
def FiniteCentralSubgroup.WitnessFor
    {ambient : ConstructiveGroup.{u}}
    (gamma : FiniteCentralSubgroup.{u, v} ambient)
    (x : ambient.Carrier) :=
  Σ' z : gamma.group.Carrier,
    ambient.Equivalent x (gamma.inclusion.toFun z)

/-! ## Algebraic central-quotient presentations -/

/-- Constructive algebraic presentation of a quotient by a finite central
subgroup.

The `surjective_lift` field returns a representative in `coverGroup` for every
quotient representative.  Exactness of the kernel is recorded in both
computational directions: a kernel proof produces a representative in the
specified finite central subgroup `gamma`, and an explicit `gamma`
representative produces a kernel proof.

This structure contains no proof that `coverGroup` is topologically simply
connected.  It also contains no topology or compactness data; see the module
boundary above. -/
structure CentralQuotientPresentation
    (coverGroup : ConstructiveGroup.{u})
    (quotientGroup : ConstructiveGroup.{v}) where
  /-- The finite central subgroup being divided out. -/
  gamma : FiniteCentralSubgroup.{u, w} coverGroup
  /-- The quotient homomorphism on representatives. -/
  quotient_hom : ConstructiveGroup.Hom coverGroup quotientGroup
  /-- Constructive surjectivity: compute a lift and its correctness proof. -/
  surjective_lift : (g : quotientGroup.Carrier) →
    Σ' x : coverGroup.Carrier,
      quotientGroup.Equivalent (quotient_hom.toFun x) g
  /-- Exact-kernel forward map: a kernel element yields explicit `gamma` data. -/
  kernel_to_gamma : (x : coverGroup.Carrier) →
    quotientGroup.Equivalent (quotient_hom.toFun x) quotientGroup.one →
      gamma.WitnessFor x
  /-- Exact-kernel reverse map: explicit `gamma` data yields a kernel proof. -/
  gamma_to_kernel : (x : coverGroup.Carrier) →
    gamma.WitnessFor x →
      quotientGroup.Equivalent (quotient_hom.toFun x) quotientGroup.one

/-! ## Derived central-quotient laws -/

/-- Every included central element maps to the quotient identity. -/
theorem CentralQuotientPresentation.quotient_inclusion_equiv_one
    {coverGroup : ConstructiveGroup.{u}}
    {quotientGroup : ConstructiveGroup.{v}}
    (Q : CentralQuotientPresentation.{u, v, w}
      coverGroup quotientGroup)
    (z : Q.gamma.group.Carrier) :
    quotientGroup.Equivalent
      (Q.quotient_hom.toFun (Q.gamma.inclusion.toFun z))
      quotientGroup.one :=
  Q.gamma_to_kernel (Q.gamma.inclusion.toFun z)
    ⟨z, coverGroup.equivalent_refl _⟩

/-- Right multiplication by an included central element does not change the
quotient element. -/
theorem CentralQuotientPresentation.quotient_mul_right_gamma_equiv
    {coverGroup : ConstructiveGroup.{u}}
    {quotientGroup : ConstructiveGroup.{v}}
    (Q : CentralQuotientPresentation.{u, v, w}
      coverGroup quotientGroup)
    (x : coverGroup.Carrier) (z : Q.gamma.group.Carrier) :
    quotientGroup.Equivalent
      (Q.quotient_hom.toFun
        (coverGroup.mul x (Q.gamma.inclusion.toFun z)))
      (Q.quotient_hom.toFun x) := by
  exact quotientGroup.equivalent_trans
    (Q.quotient_hom.map_mul x (Q.gamma.inclusion.toFun z))
    (quotientGroup.equivalent_trans
      (quotientGroup.mul_congr
        (quotientGroup.equivalent_refl _)
        (Q.quotient_inclusion_equiv_one z))
      (quotientGroup.mul_one _))

/-- Left multiplication by an included central element does not change the
quotient element. -/
theorem CentralQuotientPresentation.quotient_mul_left_gamma_equiv
    {coverGroup : ConstructiveGroup.{u}}
    {quotientGroup : ConstructiveGroup.{v}}
    (Q : CentralQuotientPresentation.{u, v, w}
      coverGroup quotientGroup)
    (z : Q.gamma.group.Carrier) (x : coverGroup.Carrier) :
    quotientGroup.Equivalent
      (Q.quotient_hom.toFun
        (coverGroup.mul (Q.gamma.inclusion.toFun z) x))
      (Q.quotient_hom.toFun x) := by
  exact quotientGroup.equivalent_trans
    (Q.quotient_hom.map_mul (Q.gamma.inclusion.toFun z) x)
    (quotientGroup.equivalent_trans
      (quotientGroup.mul_congr
        (Q.quotient_inclusion_equiv_one z)
        (quotientGroup.equivalent_refl _))
      (quotientGroup.one_mul _))

/-- Semantically equivalent representatives that differ on the right by an
included central element have the same quotient image. -/
theorem CentralQuotientPresentation.quotient_equiv_of_right_gamma
    {coverGroup : ConstructiveGroup.{u}}
    {quotientGroup : ConstructiveGroup.{v}}
    (Q : CentralQuotientPresentation.{u, v, w}
      coverGroup quotientGroup)
    {x y : coverGroup.Carrier} (z : Q.gamma.group.Carrier)
    (h : coverGroup.Equivalent x
      (coverGroup.mul y (Q.gamma.inclusion.toFun z))) :
    quotientGroup.Equivalent
      (Q.quotient_hom.toFun x) (Q.quotient_hom.toFun y) :=
  quotientGroup.equivalent_trans
    (Q.quotient_hom.map_equivalent h)
    (Q.quotient_mul_right_gamma_equiv y z)

/-- Semantically equivalent representatives that differ on the left by an
included central element have the same quotient image. -/
theorem CentralQuotientPresentation.quotient_equiv_of_left_gamma
    {coverGroup : ConstructiveGroup.{u}}
    {quotientGroup : ConstructiveGroup.{v}}
    (Q : CentralQuotientPresentation.{u, v, w}
      coverGroup quotientGroup)
    {x y : coverGroup.Carrier} (z : Q.gamma.group.Carrier)
    (h : coverGroup.Equivalent x
      (coverGroup.mul (Q.gamma.inclusion.toFun z) y)) :
    quotientGroup.Equivalent
      (Q.quotient_hom.toFun x) (Q.quotient_hom.toFun y) :=
  quotientGroup.equivalent_trans
    (Q.quotient_hom.map_equivalent h)
    (Q.quotient_mul_left_gamma_equiv z y)

end ConstructiveGroups

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms ConstructiveGroups.ConstructiveGroup.equivalent_refl
#print axioms ConstructiveGroups.ConstructiveGroup.equivalent_symm
#print axioms ConstructiveGroups.ConstructiveGroup.equivalent_trans
#print axioms ConstructiveGroups.CentralQuotientPresentation.quotient_inclusion_equiv_one
#print axioms ConstructiveGroups.CentralQuotientPresentation.quotient_mul_right_gamma_equiv
#print axioms ConstructiveGroups.CentralQuotientPresentation.quotient_mul_left_gamma_equiv
#print axioms ConstructiveGroups.CentralQuotientPresentation.quotient_equiv_of_right_gamma
#print axioms ConstructiveGroups.CentralQuotientPresentation.quotient_equiv_of_left_gamma
