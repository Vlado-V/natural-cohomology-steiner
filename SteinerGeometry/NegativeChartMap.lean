import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomChart

/-! Actual negative-twist maps in the normalized standard-chart frame. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.NegativeChartMap
open CategoryTheory AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- On its distinguished affine chart, an actual line-sheaf map acts by
multiplication by the coefficient of its encoding section. -/
theorem map_chartCoefficient (j : σ) (a b : ℕ) (hba : b ≤ a)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b)
    (x : Γ(TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a,
      MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)) :
    NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneNegativeChartCoefficient j b
        (f.val.app (op (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)) x) =
      NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneNegativeChartCoefficient j a x *
        PolynomialSectionProductCriterion.MvPolynomial.coordinateTwistChartCoefficient
          (R := R) j j (a - b)
          (NegativeTwistHomSections.MvPolynomial.coordinateNegativeTwistHomSection
            (R := R) j a b hba f) := by
  conv_lhs =>
    rw [NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneIdealChartPowerSection_generates
      (R := R) j a x]
  rw [map_smul, NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneNegativeChartCoefficient_smul]
  rw [NegativeTwistHomChart.MvPolynomial.coordinateNegativeTwistHomSection_chartCoefficient]
  rfl

end SteinerGeometry.NegativeChartMap
