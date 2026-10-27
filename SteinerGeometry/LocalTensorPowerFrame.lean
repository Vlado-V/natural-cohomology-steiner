import SteinerGeometry.LocalTensorFrames
import OAI.AlgebraicGeometry.SheafCohomology.Projective.LocalPowerSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.UnitFrameSection

/-! The recursive negative-power frame evaluates recursive local tensor powers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.LocalTensorPowerFrame
open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective
open LocalTensorFrames
universe u
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
local instance localTensorPowerFrame_monoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

theorem idealLocalTensorPower_coefficient (j : σ)
    (U : (Proj (MvPolynomial.homogeneousSubmodule σ R)).affineOpens)
    (e : (IdealModule.idealModule
      (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)).restrict U.1.ι ≅
      Invertible.Scheme.Modules.unitObj U.1.toScheme)
    (x : Γ(IdealModule.idealModule
      (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j), U.1)) (n : ℕ) :
    coefficient (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n)
      U (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivializationOf U.1 j e n)
      (LocalPowerSections.MvPolynomial.coordinateHyperplaneIdealLocalTensorPower j U.1 x n) =
      (coefficient _ U e x) ^ n := by
  induction n with
  | zero =>
    rw [LocalPowerSections.MvPolynomial.coordinateHyperplaneIdealLocalTensorPower,
      RestrictedUnitTensorSection.localMonoidalUnitSection_eq_restrict, pow_zero]
    change FrameSections.localTrivializationTopSection
      (𝟙_ (Proj (MvPolynomial.homogeneousSubmodule σ R)).Modules)
      U (TensorSections.restrictMonoidalUnitIso U.1.ι ≪≫
        TensorSections.monoidalUnitObjIso U.1.toScheme)
      (TensorSections.monoidalUnitSection _) = 1
    exact UnitFrameSection.localTrivializationTopSection_monoidalUnitSection U
  | succ n ih =>
    change coefficient (_ ⊗ _) U
      (TensorSections.restrictMonoidalTensorIso U.1.ι _ _ ≪≫
        (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivializationOf
          U.1 j e n ⊗ᵢ e) ≪≫ TensorSections.unitObjTensorIso U.1.toScheme)
      (TensorSections.tensorSection _ _ U.1
        (LocalPowerSections.MvPolynomial.coordinateHyperplaneIdealLocalTensorPower j U.1 x n) x) = _
    rw [coefficient_tensorSection, ih, pow_succ]

end SteinerGeometry.LocalTensorPowerFrame
