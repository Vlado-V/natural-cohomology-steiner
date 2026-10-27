module

public import SteinerGeometry.TensorSwapUnitIso

set_option backward.privateInPublic true
@[expose] public section

/-! The shared negative-power tensor isomorphism, with native power endpoints. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SteinerGeometry.NegativePowerTensorIso
open CategoryTheory AlgebraicGeometry MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] TwistPowers.MvPolynomial.instMonoidalCategoryModules_oAI

/-- Remove the unit in the first negative power and exchange the two factors. -/
def iso (j : σ) (d : ℕ) :
    TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j 1 ⊗
        TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j d ≅
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d+1) :=
  TensorSwapUnitIso.iso
    (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
    (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j d)

end SteinerGeometry.NegativePowerTensorIso
