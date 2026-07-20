/-
Constructive descent of group homomorphisms through explicit central quotients.

# Scope

Given an algebraic central-quotient presentation

  coverGroup --Q--> quotientGroup

and a homomorphism `rho : coverGroup -> target`, this module constructs the
descended homomorphism whenever every explicitly included element of `Gamma`
maps to the target identity.  The construction uses `Q.surjective_lift`, so it
does not choose representatives classically.  Exactness of `Q` supplies a
`PSigma` witness whenever two lifts have the same quotient image.

The descended homomorphism is faithful exactly when every element killed by
`rho` constructively produces a `Gamma.WitnessFor`.  Together with the descent
hypothesis this is the witness-bearing statement `ker(rho) = Gamma`; no
propositionally truncated existence claim is used.

# Boundary

This is algebraic representation descent for `ConstructiveGroup.Hom`.  It does
not construct vector spaces, matrices, continuity, unitarity, compactness, or
Haar integration.  Those structures can instantiate `target` later.

# Constructivity

The only import is the Lean-core constructive-group leaf.  There is no
Classical reasoning, choice, `Nonempty`, quotient, `noncomputable`, `Exists`,
axiom, or `sorry` in this file.
-/

import ConstructiveGroups.ConstructiveGroup

universe u v w x

namespace ConstructiveGroups

/-! ## Constructive setoid-group calculus -/

/-- Left cancellation in a constructive setoid group. -/
theorem ConstructiveGroup.mul_left_cancel
    (G : ConstructiveGroup.{u}) {a b c : G.Carrier}
    (h : G.Equivalent (G.mul a b) (G.mul a c)) :
    G.Equivalent b c := by
  apply G.equivalent_trans (G.equivalent_symm (G.one_mul b))
  apply G.equivalent_trans
    (G.mul_congr (G.equivalent_symm (G.inv_mul a))
      (G.equivalent_refl b))
  apply G.equivalent_trans (G.mul_assoc (G.inv a) a b)
  apply G.equivalent_trans
    (G.mul_congr (G.equivalent_refl (G.inv a)) h)
  apply G.equivalent_trans
    (G.equivalent_symm (G.mul_assoc (G.inv a) a c))
  apply G.equivalent_trans
    (G.mul_congr (G.inv_mul a) (G.equivalent_refl c))
  exact G.one_mul c

/-- Right cancellation in a constructive setoid group. -/
theorem ConstructiveGroup.mul_right_cancel
    (G : ConstructiveGroup.{u}) {a b c : G.Carrier}
    (h : G.Equivalent (G.mul b a) (G.mul c a)) :
    G.Equivalent b c := by
  apply G.equivalent_trans (G.equivalent_symm (G.mul_one b))
  apply G.equivalent_trans
    (G.mul_congr (G.equivalent_refl b)
      (G.equivalent_symm (G.mul_inv a)))
  apply G.equivalent_trans
    (G.equivalent_symm (G.mul_assoc b a (G.inv a)))
  apply G.equivalent_trans
    (G.mul_congr h (G.equivalent_refl (G.inv a)))
  apply G.equivalent_trans (G.mul_assoc c a (G.inv a))
  apply G.equivalent_trans
    (G.mul_congr (G.equivalent_refl c) (G.mul_inv a))
  exact G.mul_one c

/-- If `x⁻¹y` is semantically the identity, then `x` and `y` are
semantically equivalent. -/
theorem ConstructiveGroup.equivalent_of_inv_mul_equiv_one
    (G : ConstructiveGroup.{u}) {a b : G.Carrier}
    (h : G.Equivalent (G.mul (G.inv a) b) G.one) :
    G.Equivalent a b := by
  apply G.equivalent_symm
  apply G.mul_left_cancel (a := G.inv a)
  apply G.equivalent_trans h
  exact G.equivalent_symm (G.inv_mul a)

namespace ConstructiveGroup.Hom

/-- A constructive-group homomorphism is faithful when it reflects semantic
equivalence.  This is injectivity on the represented setoid, not raw carrier
equality. -/
def Faithful
    {source : ConstructiveGroup.{u}} {target : ConstructiveGroup.{v}}
    (f : ConstructiveGroup.Hom source target) : Prop :=
  ∀ {a b : source.Carrier},
    target.Equivalent (f.toFun a) (f.toFun b) → source.Equivalent a b

/-- Homomorphisms of constructive groups preserve inversion modulo the target
setoid. -/
theorem map_inv
    {source : ConstructiveGroup.{u}} {target : ConstructiveGroup.{v}}
    (f : ConstructiveGroup.Hom source target) (a : source.Carrier) :
    target.Equivalent (f.toFun (source.inv a)) (target.inv (f.toFun a)) := by
  apply target.mul_right_cancel (a := f.toFun a)
  apply target.equivalent_trans
    (target.equivalent_symm (f.map_mul (source.inv a) a))
  apply target.equivalent_trans (f.map_equivalent (source.inv_mul a))
  apply target.equivalent_trans f.map_one
  exact target.equivalent_symm (target.inv_mul (f.toFun a))

/-- Equivalent images force the image of `a⁻¹b` to be the target identity. -/
theorem image_inv_mul_equiv_one_of_images_equivalent
    {source : ConstructiveGroup.{u}} {target : ConstructiveGroup.{v}}
    (f : ConstructiveGroup.Hom source target) {a b : source.Carrier}
    (h : target.Equivalent (f.toFun a) (f.toFun b)) :
    target.Equivalent (f.toFun (source.mul (source.inv a) b)) target.one := by
  apply target.equivalent_trans (f.map_mul (source.inv a) b)
  apply target.equivalent_trans
    (target.mul_congr (f.map_inv a) (target.equivalent_refl (f.toFun b)))
  apply target.equivalent_trans
    (target.mul_congr (target.inv_congr h)
      (target.equivalent_refl (f.toFun b)))
  exact target.inv_mul (f.toFun b)

/-- If the image of `a⁻¹b` is the target identity, then the images of `a` and
`b` are semantically equivalent. -/
theorem images_equivalent_of_image_inv_mul_equiv_one
    {source : ConstructiveGroup.{u}} {target : ConstructiveGroup.{v}}
    (f : ConstructiveGroup.Hom source target) {a b : source.Carrier}
    (h : target.Equivalent
      (f.toFun (source.mul (source.inv a) b)) target.one) :
    target.Equivalent (f.toFun a) (f.toFun b) := by
  apply target.equivalent_of_inv_mul_equiv_one
  apply target.equivalent_trans
    (target.mul_congr
      (target.equivalent_symm (f.map_inv a))
      (target.equivalent_refl (f.toFun b)))
  apply target.equivalent_trans
    (target.equivalent_symm (f.map_mul (source.inv a) b))
  exact h

/-- Constructive kernel criterion for faithfulness. -/
theorem faithful_iff_kernel_trivial
    {source : ConstructiveGroup.{u}} {target : ConstructiveGroup.{v}}
    (f : ConstructiveGroup.Hom source target) :
    f.Faithful ↔
      ∀ a : source.Carrier,
        target.Equivalent (f.toFun a) target.one →
          source.Equivalent a source.one := by
  constructor
  · intro hfaithful a ha
    apply hfaithful
    apply target.equivalent_trans ha
    exact target.equivalent_symm f.map_one
  · intro hkernel a b hab
    apply source.equivalent_of_inv_mul_equiv_one
    apply hkernel
    exact f.image_inv_mul_equiv_one_of_images_equivalent hab

end ConstructiveGroup.Hom

/-! ## Gamma-trivial homomorphisms and explicit kernel witnesses -/

/-- `rho` kills an explicitly presented finite central subgroup when every
included subgroup representative maps to the target identity. -/
def FiniteCentralSubgroup.IsKilledBy
    {ambient : ConstructiveGroup.{u}}
    (gamma : FiniteCentralSubgroup.{u, v} ambient)
    {target : ConstructiveGroup.{w}}
    (rho : ConstructiveGroup.Hom ambient target) : Prop :=
  ∀ z : gamma.group.Carrier,
    target.Equivalent
      (rho.toFun (gamma.inclusion.toFun z)) target.one

/-- Killing the included subgroup kills every ambient representative carrying
an explicit witness that it belongs to that subgroup. -/
theorem FiniteCentralSubgroup.image_equiv_one_of_witness
    {ambient : ConstructiveGroup.{u}}
    (gamma : FiniteCentralSubgroup.{u, v} ambient)
    {target : ConstructiveGroup.{w}}
    (rho : ConstructiveGroup.Hom ambient target)
    (hGamma : gamma.IsKilledBy rho)
    {a : ambient.Carrier} (witness : gamma.WitnessFor a) :
    target.Equivalent (rho.toFun a) target.one := by
  apply target.equivalent_trans (rho.map_equivalent witness.snd)
  exact hGamma witness.fst

/-- Witness-bearing reverse kernel inclusion for a representation of the
cover: every representative killed by `rho` computes an element of `Gamma`
representing it.  Combined with `Gamma.IsKilledBy rho`, this is the exact
kernel statement `ker(rho) = Gamma`. -/
def CentralQuotientPresentation.RepresentationKernelHasGammaWitness
    {coverGroup : ConstructiveGroup.{u}}
    {quotientGroup : ConstructiveGroup.{v}}
    (Q : CentralQuotientPresentation.{u, v, w}
      coverGroup quotientGroup)
    {target : ConstructiveGroup.{x}}
    (rho : ConstructiveGroup.Hom coverGroup target) : Type (max u w) :=
  ∀ a : coverGroup.Carrier,
    target.Equivalent (rho.toFun a) target.one → Q.gamma.WitnessFor a

/-! ## Descent through an explicit central quotient -/

/-- Equal quotient images have equal `rho` images whenever `rho` kills
`Gamma`.  The proof obtains a computable `Gamma` witness for `a⁻¹b` from the
exact quotient kernel. -/
theorem CentralQuotientPresentation.images_equivalent_of_quotient_equivalent
    {coverGroup : ConstructiveGroup.{u}}
    {quotientGroup : ConstructiveGroup.{v}}
    (Q : CentralQuotientPresentation.{u, v, w}
      coverGroup quotientGroup)
    {target : ConstructiveGroup.{x}}
    (rho : ConstructiveGroup.Hom coverGroup target)
    (hGamma : Q.gamma.IsKilledBy rho)
    {a b : coverGroup.Carrier}
    (h : quotientGroup.Equivalent
      (Q.quotient_hom.toFun a) (Q.quotient_hom.toFun b)) :
    target.Equivalent (rho.toFun a) (rho.toFun b) := by
  apply rho.images_equivalent_of_image_inv_mul_equiv_one
  apply Q.gamma.image_equiv_one_of_witness rho hGamma
  apply Q.kernel_to_gamma
  exact Q.quotient_hom.image_inv_mul_equiv_one_of_images_equivalent h

/-- Construct the descended homomorphism using the representative returned by
`Q.surjective_lift`.  No representative choice is hidden: the lift is a field
of the quotient presentation, and the preceding fiber theorem proves that the
result respects semantic equality. -/
def CentralQuotientPresentation.descendRepresentation
    {coverGroup : ConstructiveGroup.{u}}
    {quotientGroup : ConstructiveGroup.{v}}
    (Q : CentralQuotientPresentation.{u, v, w}
      coverGroup quotientGroup)
    {target : ConstructiveGroup.{x}}
    (rho : ConstructiveGroup.Hom coverGroup target)
    (hGamma : Q.gamma.IsKilledBy rho) :
    ConstructiveGroup.Hom quotientGroup target where
  toFun := fun g => rho.toFun (Q.surjective_lift g).fst
  map_equivalent := by
    intro g h hgh
    apply Q.images_equivalent_of_quotient_equivalent rho hGamma
    apply quotientGroup.equivalent_trans (Q.surjective_lift g).snd
    apply quotientGroup.equivalent_trans hgh
    exact quotientGroup.equivalent_symm (Q.surjective_lift h).snd
  map_one := by
    apply Q.gamma.image_equiv_one_of_witness rho hGamma
    exact Q.kernel_to_gamma
      (Q.surjective_lift quotientGroup.one).fst
      (Q.surjective_lift quotientGroup.one).snd
  map_mul := by
    intro g h
    apply target.equivalent_trans
      (Q.images_equivalent_of_quotient_equivalent rho hGamma
        (a := (Q.surjective_lift (quotientGroup.mul g h)).fst)
        (b := coverGroup.mul
          (Q.surjective_lift g).fst (Q.surjective_lift h).fst)
        (by
          apply quotientGroup.equivalent_trans
            (Q.surjective_lift (quotientGroup.mul g h)).snd
          apply quotientGroup.equivalent_symm
          apply quotientGroup.equivalent_trans
            (Q.quotient_hom.map_mul
              (Q.surjective_lift g).fst (Q.surjective_lift h).fst)
          exact quotientGroup.mul_congr
            (Q.surjective_lift g).snd (Q.surjective_lift h).snd))
    exact rho.map_mul (Q.surjective_lift g).fst
      (Q.surjective_lift h).fst

/-- The constructed descent commutes with the quotient map modulo the target
setoid. -/
theorem CentralQuotientPresentation.descendRepresentation_quotient_hom
    {coverGroup : ConstructiveGroup.{u}}
    {quotientGroup : ConstructiveGroup.{v}}
    (Q : CentralQuotientPresentation.{u, v, w}
      coverGroup quotientGroup)
    {target : ConstructiveGroup.{x}}
    (rho : ConstructiveGroup.Hom coverGroup target)
    (hGamma : Q.gamma.IsKilledBy rho) (a : coverGroup.Carrier) :
    target.Equivalent
      ((Q.descendRepresentation rho hGamma).toFun
        (Q.quotient_hom.toFun a))
      (rho.toFun a) :=
  Q.images_equivalent_of_quotient_equivalent rho hGamma
    (Q.surjective_lift (Q.quotient_hom.toFun a)).snd

/-- Faithfulness of the descended representation computes the reverse-kernel
witness function.  This is a `def`, not a Prop-level existential: callers can
project and use the returned central representative. -/
def CentralQuotientPresentation.kernelGammaWitness_of_descendFaithful
    {coverGroup : ConstructiveGroup.{u}}
    {quotientGroup : ConstructiveGroup.{v}}
    (Q : CentralQuotientPresentation.{u, v, w}
      coverGroup quotientGroup)
    {target : ConstructiveGroup.{x}}
    (rho : ConstructiveGroup.Hom coverGroup target)
    (hGamma : Q.gamma.IsKilledBy rho)
    (hfaithful : (Q.descendRepresentation rho hGamma).Faithful) :
    Q.RepresentationKernelHasGammaWitness rho := by
  have hkernel :=
    (ConstructiveGroup.Hom.faithful_iff_kernel_trivial
      (Q.descendRepresentation rho hGamma)).mp hfaithful
  intro a ha
  apply Q.kernel_to_gamma a
  apply hkernel (Q.quotient_hom.toFun a)
  apply target.equivalent_trans
    (Q.descendRepresentation_quotient_hom rho hGamma a)
  exact ha

/-- Conversely, explicit reverse-kernel witnesses prove faithfulness of the
descent.  Together with `kernelGammaWitness_of_descendFaithful`, this gives the
two constructive directions of the exact criterion.  They are deliberately
not packaged as Prop-level `Iff`, because the witness function lives in
`Type` and must retain its computational content. -/
theorem CentralQuotientPresentation.descendFaithful_of_kernelGammaWitness
    {coverGroup : ConstructiveGroup.{u}}
    {quotientGroup : ConstructiveGroup.{v}}
    (Q : CentralQuotientPresentation.{u, v, w}
      coverGroup quotientGroup)
    {target : ConstructiveGroup.{x}}
    (rho : ConstructiveGroup.Hom coverGroup target)
    (hGamma : Q.gamma.IsKilledBy rho)
    (hwitness : Q.RepresentationKernelHasGammaWitness rho) :
    (Q.descendRepresentation rho hGamma).Faithful := by
  apply (ConstructiveGroup.Hom.faithful_iff_kernel_trivial
    (Q.descendRepresentation rho hGamma)).mpr
  intro g hg
  apply quotientGroup.equivalent_trans
    (quotientGroup.equivalent_symm (Q.surjective_lift g).snd)
  apply Q.gamma_to_kernel
  exact hwitness (Q.surjective_lift g).fst hg

end ConstructiveGroups

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms ConstructiveGroups.ConstructiveGroup.mul_left_cancel
#print axioms ConstructiveGroups.ConstructiveGroup.mul_right_cancel
#print axioms ConstructiveGroups.ConstructiveGroup.equivalent_of_inv_mul_equiv_one
#print axioms ConstructiveGroups.ConstructiveGroup.Hom.map_inv
#print axioms ConstructiveGroups.ConstructiveGroup.Hom.image_inv_mul_equiv_one_of_images_equivalent
#print axioms ConstructiveGroups.ConstructiveGroup.Hom.images_equivalent_of_image_inv_mul_equiv_one
#print axioms ConstructiveGroups.ConstructiveGroup.Hom.faithful_iff_kernel_trivial
#print axioms ConstructiveGroups.FiniteCentralSubgroup.image_equiv_one_of_witness
#print axioms ConstructiveGroups.CentralQuotientPresentation.images_equivalent_of_quotient_equivalent
#print axioms ConstructiveGroups.CentralQuotientPresentation.descendRepresentation_quotient_hom
#print axioms ConstructiveGroups.CentralQuotientPresentation.kernelGammaWitness_of_descendFaithful
#print axioms ConstructiveGroups.CentralQuotientPresentation.descendFaithful_of_kernelGammaWitness
