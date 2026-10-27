module

public import SteinerGeometry.ProjectiveSteinerBundle
public import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorConjugatedMapSections

set_option backward.privateInPublic true
@[expose] public section

/-! The actual line-twist map in its canonical tensor coordinates. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000

namespace SteinerGeometry.ProjectiveSteinerBundle
open CategoryTheory AlgebraicGeometry MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] TwistPowers.MvPolynomial.instMonoidalCategoryModules_oAI

private theorem tensorMap_eq_conjugated {X : Scheme.{u}} {A B T P Q : X.Modules}
    (eS : A ⊗ T ≅ P) (eT : B ⊗ T ≅ Q) (f : A ⟶ B) :
    eS.inv ≫ (f ▷ T) ≫ eT.hom =
      TensorConjugatedMapSections.tensorConjugatedMap eS eT f := by
  simp only [TensorConjugatedMapSections.tensorConjugatedMap, tensorHom_id]

/-- The normalized map of an actual tensor twist is its literal tensor conjugate. -/
theorem lineMap_eq_conjugated (n : ℕ) (b : ℤ)
    (f : projectiveTwist R n (-1) ⟶ projectiveTwist R n 0) :
    (minusOneLineTwistIso (R := R) n b).inv ≫
        (twistEquivalence (R := R) n b).functor.map f ≫
          (zeroLineTwistIso (R := R) n b).hom =
      TensorConjugatedMapSections.tensorConjugatedMap
        (minusOneLineTwistIso (R := R) n b) (zeroLineTwistIso (R := R) n b) f := by
  rw [twistEquivalence_map]
  exact tensorMap_eq_conjugated _ _ _

end SteinerGeometry.ProjectiveSteinerBundle
