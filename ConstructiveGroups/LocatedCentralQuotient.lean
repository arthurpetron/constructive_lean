/-
Constructive located central-coset presentations for finite central
subgroups.

# Scope

Given a constructive setoid group `ambient`, a finite central subgroup
`gamma`, and a locator deciding right-multiplication coset witnesses as
Type-level data, this module equips the raw carrier of `ambient` with the
coarser central-coset setoid.  The raw multiplication and inversion then form
a constructive group, and the identity function on representatives is an
exact central-quotient homomorphism.  The equation used below is
`x = y * i(z)`, so in the standard convention it describes the left coset
`y * gamma`; because `gamma` is central, left and right cosets coincide.

The semantic relation intentionally stores only `Nonempty` witness data.  It
is therefore a proposition suitable for a `Setoid`, while the locator remains
outside `Prop` and can recompute the explicit central representative required
by `CentralQuotientPresentation.kernel_to_gamma`.  In the locator's negative
branch, the truncated semantic proof is eliminated only into `False`; the
resulting contradiction then eliminates into the required witness type.

# Boundary

The carrier is a setoid presentation on the same raw representatives, not a
chosen-normal-form carrier.  Finiteness of `gamma` alone does not construct a
locator because the ambient semantic equality need not be decidable; the
locator is explicit input.  This module asserts no topology, compactness,
smoothness, Haar integration, simple connectedness, or Lie-group realization.

# Constructivity

The only import is the constructive representation-descent leaf.  There is no
classical reasoning, implicit or canonical representative selection, actual
quotient type, noncomputable declaration, custom axiom, admitted proof, or
compiler-backed decision procedure in this file.  The setoid relation does
use `Nonempty` as a propositional truncation, but no witness is extracted
directly from that truncation: on the sole Type-valued path, output comes from
the explicit locator, while the negative branch uses `Nonempty` only to derive
`False`.
-/

import ConstructiveGroups.ConstructiveRepresentationDescent

universe u v

namespace ConstructiveGroups

/-! ## Type-level location and central-coset semantics -/

/-- A Type-level result carrying either usable data of type `A` or a function
refuting every such datum.

Unlike a decision on a proposition, the positive branch retains the witness
as computational data. -/
inductive WitnessOrRefutation (A : Type u) : Type u where
  /-- A located witness. -/
  | witness (value : A)
  /-- A constructive refutation of every putative witness. -/
  | refutation (reject : A → False)

/-- Explicit data witnessing that `x` and `y` differ on the right by an
included element of `gamma`. -/
def FiniteCentralSubgroup.CentralCosetWitness
    {ambient : ConstructiveGroup.{u}}
    (gamma : FiniteCentralSubgroup.{u, v} ambient)
    (x y : ambient.Carrier) : Type v :=
  Σ' z : gamma.group.Carrier,
    ambient.Equivalent x
      (ambient.mul y (gamma.inclusion.toFun z))

/-- A locator for central-coset witnesses.

For every pair of ambient representatives it computes either an explicit
central representative or a function refuting every such representative.
This is Type-level data, not a proof-irrelevant decidability assertion. -/
def FiniteCentralSubgroup.Locator
    {ambient : ConstructiveGroup.{u}}
    (gamma : FiniteCentralSubgroup.{u, v} ambient) : Type (max u v) :=
  (x y : ambient.Carrier) →
    WitnessOrRefutation (gamma.CentralCosetWitness x y)

/-! ### Constructive finite search -/

/-- Search a finite index type without erasing the successful index.

The positive branch returns the first successful slot encountered by the
zero-then-successor recursion.  The negative branch refutes a putative slot by
the same recursion. -/
def WitnessOrRefutation.locateFin :
    (n : Nat) →
    (P : Fin n → Prop) →
    ((i : Fin n) → Decidable (P i)) →
    WitnessOrRefutation (Σ' i : Fin n, P i)
  | 0, _, _ =>
      .refutation (fun located => Fin.elim0 located.fst)
  | Nat.succ n, P, decideP =>
      match decideP ⟨0, Nat.zero_lt_succ n⟩ with
      | isTrue hzero =>
          .witness ⟨⟨0, Nat.zero_lt_succ n⟩, hzero⟩
      | isFalse hzero =>
          match WitnessOrRefutation.locateFin n
              (fun i => P i.succ) (fun i => decideP i.succ) with
          | .witness located =>
              .witness ⟨located.fst.succ, located.snd⟩
          | .refutation rejectTail =>
              .refutation (fun located =>
                Fin.cases hzero
                  (fun i hi => rejectTail ⟨i, hi⟩)
                  located.fst located.snd)

/-- A decidable ambient semantic equality produces a central-coset locator by
searching the supplied finite enumeration of `gamma`.

The negative branch is stronger than failure on the enumerated slots: for an
arbitrary subgroup representative, `finite.cover` computes a representing
slot, and congruence of the inclusion transports any alleged central-coset
witness back to that rejected slot.  Thus repetitions in the enumeration are
harmless and no decidable equality on subgroup representatives is required. -/
def FiniteCentralSubgroup.Locator.ofDecidableEquivalent
    {ambient : ConstructiveGroup.{u}}
    (gamma : FiniteCentralSubgroup.{u, v} ambient)
    (decidableEquivalent : (x y : ambient.Carrier) →
      Decidable (ambient.Equivalent x y)) :
    gamma.Locator := by
  intro x y
  let slotPredicate : Fin gamma.finite.size → Prop := fun i =>
    ambient.Equivalent x
      (ambient.mul y
        (gamma.inclusion.toFun (gamma.finite.enumerate i)))
  let slotDecision : (i : Fin gamma.finite.size) →
      Decidable (slotPredicate i) := fun i =>
    decidableEquivalent x
      (ambient.mul y
        (gamma.inclusion.toFun (gamma.finite.enumerate i)))
  match WitnessOrRefutation.locateFin gamma.finite.size
      slotPredicate slotDecision with
  | .witness located =>
      exact .witness
        ⟨gamma.finite.enumerate located.fst, located.snd⟩
  | .refutation rejectSlots =>
      exact .refutation (fun alleged =>
        let covered := gamma.finite.cover alleged.fst
        rejectSlots ⟨covered.fst,
          ambient.equivalent_trans alleged.snd
            (ambient.mul_congr (ambient.equivalent_refl y)
              (ambient.equivalent_symm
                (gamma.inclusion.map_equivalent covered.snd)))⟩)

/-- Prop-valued right-multiplication coset equality.  This is the sole point
at which an explicit coset witness is propositionally truncated.  Under the
standard naming convention the equation `x = y * i(z)` describes equality in
the left-coset space; centrality makes the left/right distinction immaterial. -/
def FiniteCentralSubgroup.CentralCosetEquivalent
    {ambient : ConstructiveGroup.{u}}
    (gamma : FiniteCentralSubgroup.{u, v} ambient)
    (x y : ambient.Carrier) : Prop :=
  Nonempty (gamma.CentralCosetWitness x y)

/-! ## Explicit witness calculus -/

/-- Ambient-equivalent representatives have an explicit central-coset witness,
using the identity element of `gamma`. -/
def FiniteCentralSubgroup.centralCosetWitness_of_equivalent
    {ambient : ConstructiveGroup.{u}}
    (gamma : FiniteCentralSubgroup.{u, v} ambient)
    {x y : ambient.Carrier} (hxy : ambient.Equivalent x y) :
    gamma.CentralCosetWitness x y := by
  exact ⟨gamma.group.one,
    ambient.equivalent_trans hxy
      (ambient.equivalent_symm
        (ambient.equivalent_trans
          (ambient.mul_congr
            (ambient.equivalent_refl y) gamma.inclusion.map_one)
          (ambient.mul_one y)))⟩

/-- Ambient equivalence embeds into Prop-valued central-coset equality. -/
theorem FiniteCentralSubgroup.centralCosetEquivalent_of_equivalent
    {ambient : ConstructiveGroup.{u}}
    (gamma : FiniteCentralSubgroup.{u, v} ambient)
    {x y : ambient.Carrier} (hxy : ambient.Equivalent x y) :
    gamma.CentralCosetEquivalent x y :=
  ⟨gamma.centralCosetWitness_of_equivalent hxy⟩

/-- Construct the reverse central-coset witness by inverting its central
representative. -/
def FiniteCentralSubgroup.centralCosetWitness_symm
    {ambient : ConstructiveGroup.{u}}
    (gamma : FiniteCentralSubgroup.{u, v} ambient)
    {x y : ambient.Carrier}
    (witness : gamma.CentralCosetWitness x y) :
    gamma.CentralCosetWitness y x := by
  exact ⟨gamma.group.inv witness.fst,
    ambient.equivalent_symm
      (ambient.equivalent_trans
        (ambient.mul_congr witness.snd
          (ambient.equivalent_refl
            (gamma.inclusion.toFun (gamma.group.inv witness.fst))))
        (ambient.equivalent_trans
          (ambient.mul_assoc y (gamma.inclusion.toFun witness.fst)
            (gamma.inclusion.toFun (gamma.group.inv witness.fst)))
          (ambient.equivalent_trans
            (ambient.mul_congr (ambient.equivalent_refl y)
              (ambient.equivalent_trans
                (ambient.mul_congr
                  (ambient.equivalent_refl
                    (gamma.inclusion.toFun witness.fst))
                  (gamma.inclusion.map_inv witness.fst))
                (ambient.mul_inv (gamma.inclusion.toFun witness.fst))))
            (ambient.mul_one y))))⟩

/-- Compose explicit central-coset witnesses.  If `x = y·i(p)` and
`y = z·i(q)`, the composite witness is `q·p`. -/
def FiniteCentralSubgroup.centralCosetWitness_trans
    {ambient : ConstructiveGroup.{u}}
    (gamma : FiniteCentralSubgroup.{u, v} ambient)
    {x y z : ambient.Carrier}
    (wxy : gamma.CentralCosetWitness x y)
    (wyz : gamma.CentralCosetWitness y z) :
    gamma.CentralCosetWitness x z := by
  exact ⟨gamma.group.mul wyz.fst wxy.fst,
    ambient.equivalent_trans wxy.snd
      (ambient.equivalent_trans
        (ambient.mul_congr wyz.snd
          (ambient.equivalent_refl
            (gamma.inclusion.toFun wxy.fst)))
        (ambient.equivalent_trans
          (ambient.mul_assoc z (gamma.inclusion.toFun wyz.fst)
            (gamma.inclusion.toFun wxy.fst))
          (ambient.mul_congr (ambient.equivalent_refl z)
            (ambient.equivalent_symm
              (gamma.inclusion.map_mul wyz.fst wxy.fst)))))⟩

/-- Multiplication of representatives respects explicit central-coset
witnesses.  Centrality moves the first central factor past the second ambient
representative. -/
def FiniteCentralSubgroup.centralCosetWitness_mul
    {ambient : ConstructiveGroup.{u}}
    (gamma : FiniteCentralSubgroup.{u, v} ambient)
    {a b c d : ambient.Carrier}
    (wab : gamma.CentralCosetWitness a b)
    (wcd : gamma.CentralCosetWitness c d) :
    gamma.CentralCosetWitness (ambient.mul a c) (ambient.mul b d) := by
  exact ⟨gamma.group.mul wab.fst wcd.fst,
    ambient.equivalent_trans
      (ambient.mul_congr wab.snd wcd.snd)
      (ambient.equivalent_trans
        (ambient.mul_assoc b (gamma.inclusion.toFun wab.fst)
          (ambient.mul d (gamma.inclusion.toFun wcd.fst)))
        (ambient.equivalent_trans
          (ambient.mul_congr (ambient.equivalent_refl b)
            (ambient.equivalent_symm
              (ambient.mul_assoc (gamma.inclusion.toFun wab.fst) d
                (gamma.inclusion.toFun wcd.fst))))
          (ambient.equivalent_trans
            (ambient.mul_congr (ambient.equivalent_refl b)
              (ambient.mul_congr (gamma.central wab.fst d)
                (ambient.equivalent_refl
                  (gamma.inclusion.toFun wcd.fst))))
            (ambient.equivalent_trans
              (ambient.mul_congr (ambient.equivalent_refl b)
                (ambient.mul_assoc d (gamma.inclusion.toFun wab.fst)
                  (gamma.inclusion.toFun wcd.fst)))
              (ambient.equivalent_trans
                (ambient.equivalent_symm
                  (ambient.mul_assoc b d
                    (ambient.mul (gamma.inclusion.toFun wab.fst)
                      (gamma.inclusion.toFun wcd.fst))))
                (ambient.mul_congr
                  (ambient.equivalent_refl (ambient.mul b d))
                  (ambient.equivalent_symm
                    (gamma.inclusion.map_mul wab.fst wcd.fst))))))))⟩

/-- Inversion reverses a product in every constructive setoid group. -/
theorem ConstructiveGroup.inv_mul_reverse_equivalent
    (G : ConstructiveGroup.{u}) (a b : G.Carrier) :
    G.Equivalent (G.inv (G.mul a b))
      (G.mul (G.inv b) (G.inv a)) := by
  apply G.mul_right_cancel (a := G.mul a b)
  apply G.equivalent_trans (G.inv_mul (G.mul a b))
  apply G.equivalent_symm
  apply G.equivalent_trans
    (G.mul_assoc (G.inv b) (G.inv a) (G.mul a b))
  apply G.equivalent_trans
    (G.mul_congr (G.equivalent_refl (G.inv b))
      (G.equivalent_symm (G.mul_assoc (G.inv a) a b)))
  apply G.equivalent_trans
    (G.mul_congr (G.equivalent_refl (G.inv b))
      (G.mul_congr (G.inv_mul a) (G.equivalent_refl b)))
  apply G.equivalent_trans
    (G.mul_congr (G.equivalent_refl (G.inv b)) (G.one_mul b))
  exact G.inv_mul b

/-- Inversion respects explicit central-coset witnesses. -/
def FiniteCentralSubgroup.centralCosetWitness_inv
    {ambient : ConstructiveGroup.{u}}
    (gamma : FiniteCentralSubgroup.{u, v} ambient)
    {x y : ambient.Carrier}
    (witness : gamma.CentralCosetWitness x y) :
    gamma.CentralCosetWitness (ambient.inv x) (ambient.inv y) := by
  exact ⟨gamma.group.inv witness.fst,
    ambient.equivalent_trans (ambient.inv_congr witness.snd)
      (ambient.equivalent_trans
        (ambient.inv_mul_reverse_equivalent y
          (gamma.inclusion.toFun witness.fst))
        (ambient.equivalent_trans
          (ambient.mul_congr
            (ambient.equivalent_symm
              (gamma.inclusion.map_inv witness.fst))
            (ambient.equivalent_refl (ambient.inv y)))
          (gamma.central (gamma.group.inv witness.fst) (ambient.inv y))))⟩

/-! ## The located central-coset setoid group -/

/-- The Prop-valued central-coset relation is an equivalence relation. -/
def FiniteCentralSubgroup.centralCosetSetoid
    {ambient : ConstructiveGroup.{u}}
    (gamma : FiniteCentralSubgroup.{u, v} ambient) :
    Setoid ambient.Carrier where
  r := gamma.CentralCosetEquivalent
  iseqv := {
    refl := fun x =>
      gamma.centralCosetEquivalent_of_equivalent
        (ambient.equivalent_refl x)
    symm := by
      intro x y hxy
      apply hxy.elim
      intro witness
      exact ⟨gamma.centralCosetWitness_symm witness⟩
    trans := by
      intro x y z hxy hyz
      apply hxy.elim
      intro wxy
      apply hyz.elim
      intro wyz
      exact ⟨gamma.centralCosetWitness_trans wxy wyz⟩
  }

/-- The same raw representatives and operations as `ambient`, with semantic
equality coarsened to central-coset equality.  The locator is retained as an
explicit parameter marking this presentation as located; the group laws need
only the witness semantics, while exact-kernel extraction below uses the
locator computationally. -/
def FiniteCentralSubgroup.locatedCentralQuotientGroup
    {ambient : ConstructiveGroup.{u}}
    (gamma : FiniteCentralSubgroup.{u, v} ambient)
    (_locator : gamma.Locator) : ConstructiveGroup.{u} where
  Carrier := ambient.Carrier
  setoid := gamma.centralCosetSetoid
  one := ambient.one
  mul := ambient.mul
  inv := ambient.inv
  mul_congr := by
    intro a b c d hab hcd
    apply hab.elim
    intro wab
    apply hcd.elim
    intro wcd
    exact ⟨gamma.centralCosetWitness_mul wab wcd⟩
  inv_congr := by
    intro x y hxy
    apply hxy.elim
    intro witness
    exact ⟨gamma.centralCosetWitness_inv witness⟩
  mul_assoc := fun a b c =>
    gamma.centralCosetEquivalent_of_equivalent
      (ambient.mul_assoc a b c)
  one_mul := fun a =>
    gamma.centralCosetEquivalent_of_equivalent (ambient.one_mul a)
  mul_one := fun a =>
    gamma.centralCosetEquivalent_of_equivalent (ambient.mul_one a)
  inv_mul := fun a =>
    gamma.centralCosetEquivalent_of_equivalent (ambient.inv_mul a)
  mul_inv := fun a =>
    gamma.centralCosetEquivalent_of_equivalent (ambient.mul_inv a)

/-! ## Exact quotient presentation -/

/-- The identity function on raw representatives is the quotient
homomorphism from ambient equality to the coarser located central-coset
equality. -/
def FiniteCentralSubgroup.locatedCentralQuotientHom
    {ambient : ConstructiveGroup.{u}}
    (gamma : FiniteCentralSubgroup.{u, v} ambient)
    (locator : gamma.Locator) :
    ConstructiveGroup.Hom ambient
      (gamma.locatedCentralQuotientGroup locator) where
  toFun := fun x => x
  map_equivalent := by
    intro x y hxy
    exact gamma.centralCosetEquivalent_of_equivalent hxy
  map_one :=
    gamma.centralCosetEquivalent_of_equivalent
      (ambient.equivalent_refl ambient.one)
  map_mul := fun x y =>
    gamma.centralCosetEquivalent_of_equivalent
      (ambient.equivalent_refl (ambient.mul x y))

/-- Recompute an explicit `gamma` representative from a truncated quotient
kernel proof by consulting the locator.

The positive branch returns the locator's witness.  In the negative branch,
the truncated proof is eliminated only into `False`, after which contradiction
eliminates into the Type-level subgroup witness. -/
def FiniteCentralSubgroup.kernelWitnessFromLocator
    {ambient : ConstructiveGroup.{u}}
    (gamma : FiniteCentralSubgroup.{u, v} ambient)
    (locator : gamma.Locator) (x : ambient.Carrier)
    (hx : gamma.CentralCosetEquivalent x ambient.one) :
    gamma.WitnessFor x :=
  match locator x ambient.one with
  | .witness located =>
      ⟨located.fst,
        ambient.equivalent_trans located.snd
          (ambient.one_mul (gamma.inclusion.toFun located.fst))⟩
  | .refutation reject =>
      False.elim (Nonempty.elim hx reject)

/-- Every explicit subgroup-membership witness gives a quotient-kernel proof.
Only the semantic equality is propositionally truncated; the supplied witness
itself remains Type-level data for callers. -/
theorem FiniteCentralSubgroup.centralCosetEquivalent_one_of_witness
    {ambient : ConstructiveGroup.{u}}
    (gamma : FiniteCentralSubgroup.{u, v} ambient)
    {x : ambient.Carrier} (witness : gamma.WitnessFor x) :
    gamma.CentralCosetEquivalent x ambient.one :=
  ⟨⟨witness.fst,
    ambient.equivalent_trans witness.snd
      (ambient.equivalent_symm
        (ambient.one_mul (gamma.inclusion.toFun witness.fst)))⟩⟩

/-- The located central-coset group, identity quotient homomorphism, identity
lifts, and locator-based kernel extraction form an exact constructive central
quotient presentation. -/
def FiniteCentralSubgroup.locatedCentralQuotientPresentation
    {ambient : ConstructiveGroup.{u}}
    (gamma : FiniteCentralSubgroup.{u, v} ambient)
    (locator : gamma.Locator) :
    CentralQuotientPresentation.{u, u, v} ambient
      (gamma.locatedCentralQuotientGroup locator) where
  gamma := gamma
  quotient_hom := gamma.locatedCentralQuotientHom locator
  surjective_lift := fun g =>
    ⟨g, (gamma.locatedCentralQuotientGroup locator).equivalent_refl g⟩
  kernel_to_gamma := fun x hx =>
    gamma.kernelWitnessFromLocator locator x hx
  gamma_to_kernel := fun x witness =>
    gamma.centralCosetEquivalent_one_of_witness (x := x) witness

/-- Explicit inhabitation of the exact central-quotient-presentation type. -/
@[reducible] def FiniteCentralSubgroup.locatedCentralQuotientPresentationInhabited
    {ambient : ConstructiveGroup.{u}}
    (gamma : FiniteCentralSubgroup.{u, v} ambient)
    (locator : gamma.Locator) :
    Inhabited
      (CentralQuotientPresentation.{u, u, v} ambient
        (gamma.locatedCentralQuotientGroup locator)) :=
  ⟨gamma.locatedCentralQuotientPresentation locator⟩

end ConstructiveGroups

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms ConstructiveGroups.FiniteCentralSubgroup.centralCosetWitness_of_equivalent
#print axioms ConstructiveGroups.WitnessOrRefutation.locateFin
#print axioms ConstructiveGroups.FiniteCentralSubgroup.Locator.ofDecidableEquivalent
#print axioms ConstructiveGroups.FiniteCentralSubgroup.centralCosetEquivalent_of_equivalent
#print axioms ConstructiveGroups.FiniteCentralSubgroup.centralCosetWitness_symm
#print axioms ConstructiveGroups.FiniteCentralSubgroup.centralCosetWitness_trans
#print axioms ConstructiveGroups.FiniteCentralSubgroup.centralCosetWitness_mul
#print axioms ConstructiveGroups.ConstructiveGroup.inv_mul_reverse_equivalent
#print axioms ConstructiveGroups.FiniteCentralSubgroup.centralCosetWitness_inv
#print axioms ConstructiveGroups.FiniteCentralSubgroup.centralCosetSetoid
#print axioms ConstructiveGroups.FiniteCentralSubgroup.locatedCentralQuotientGroup
#print axioms ConstructiveGroups.FiniteCentralSubgroup.locatedCentralQuotientHom
#print axioms ConstructiveGroups.FiniteCentralSubgroup.kernelWitnessFromLocator
#print axioms ConstructiveGroups.FiniteCentralSubgroup.centralCosetEquivalent_one_of_witness
#print axioms ConstructiveGroups.FiniteCentralSubgroup.locatedCentralQuotientPresentation
#print axioms ConstructiveGroups.FiniteCentralSubgroup.locatedCentralQuotientPresentationInhabited
