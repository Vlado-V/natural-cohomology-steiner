module

public import SteinerGeometry.FrameMapCoefficient
public import SteinerGeometry.NegativeFrameCoefficient
public import SteinerGeometry.NegativeChartMap
public import SteinerGeometry.PolynomialChartRestriction

set_option backward.privateInPublic true
@[expose] public section

/-! Actual negative-twist map coefficients in the canonical chart frames. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace SteinerGeometry.NegativeMapCoefficient
open CategoryTheory AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual map scalar equals its cancellation-normalized generator value. -/
theorem coefficient_eq_negativeChartCoefficient (j : σ) (a b : ℕ)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) :
    FrameMapCoefficient.coefficient f
      (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
      (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame
        (R := R) j j a)
      (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame
        (R := R) j j b) =
    NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneNegativeChartCoefficient j b
      (f.val.app (op (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
        (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection
          (R := R) j a)) := by
  change RankOneMapCoordinates.overFrameMapCoefficient
      (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
      (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame
        (R := R) j j a)
      (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame
        (R := R) j j b) f =
    NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneNegativeChartCoefficient j b
      (f.val.app (op (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
        (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection
          (R := R) j a))
  rw [NegativeFrameCoefficient.negativeChartCoefficient_eq_overCoefficient]
  have h := RankOneMapCoordinates.overFrameMap_coordinate
    (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
    (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame
      (R := R) j j a)
    (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame
      (R := R) j j b) f
    (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection
      (R := R) j a)
  rw [NegativeFrameCoefficient.generator_overCoefficient, mul_one] at h
  exact h.symm

/-- The scalar of an actual negative-twist map is the chart coordinate of
its positive-twist encoding section. -/
theorem coefficient_eq_chartCoefficient (j : σ) (a b : ℕ) (hba : b ≤ a)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) :
    FrameMapCoefficient.coefficient f
      (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
      (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame
        (R := R) j j a)
      (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame
        (R := R) j j b) =
    PolynomialSectionProductCriterion.MvPolynomial.coordinateTwistChartCoefficient
      (R := R) j j (a - b)
      (NegativeTwistHomSections.MvPolynomial.coordinateNegativeTwistHomSection
        (R := R) j a b hba f) := by
  rw [NegativeTwistHomChart.MvPolynomial.coordinateNegativeTwistHomSection_chartCoefficient]
  exact coefficient_eq_negativeChartCoefficient j a b f

/-- Positive encoding coefficients dehomogenize to their homogeneous polynomial
on every standard intersection. -/
theorem chartCoefficient_on_intersection [Fintype σ] [LinearOrder σ]
    (j : σ) (d : ℕ)
    (x : Γ(TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j d, ⊤))
    (m : ℕ)
    (i : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) m) :
    StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) i.1
      ((Proj (MvPolynomial.homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) i.1 0)).op
        (PolynomialSectionProductCriterion.MvPolynomial.coordinateTwistChartCoefficient
          (R := R) (i.1 0).down j d x)) =
    PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (.of R), ⊤)
      (fun l => (i.1 l).down)
      (DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials
        (R := R) j d x).val := by
  exact PolynomialChartRestriction.polynomial_on_intersections
    (fun k => PolynomialSectionProductCriterion.MvPolynomial.coordinateTwistChartCoefficient
      (R := R) k j d x)
    (DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials
      (R := R) j d x).val
    (fun a => (PolynomialChartFrameCoefficient.MvPolynomial.coordinateTwistPolynomial_chartCoefficient
      j d x a).symm) m i

/-- The same positive coefficient formula with an explicitly named initial chart. -/
theorem chartCoefficient_on_intersection_of_eq [Fintype σ] [LinearOrder σ]
    (j : σ) (d : ℕ)
    (x : Γ(TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j d, ⊤))
    (m : ℕ)
    (i : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) m)
    (hi : (i.1 0).down = j) :
    StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) i.1
      ((Proj (MvPolynomial.homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (hi ▸ StandardCech.MvPolynomial.coordinateOpenCechIntersection_le
          (R := R) i.1 0)).op
        (PolynomialSectionProductCriterion.MvPolynomial.coordinateTwistChartCoefficient
          (R := R) j j d x)) =
    PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (.of R), ⊤)
      (fun l => (i.1 l).down)
      (DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials
        (R := R) j d x).val := by
  subst j
  exact chartCoefficient_on_intersection (i.1 0).down d x m i

/-- On an intersection retaining the distinguished first chart, the actual map
coefficient is exactly the dehomogenization of its encoding polynomial. -/
theorem coefficient_on_intersection [Fintype σ] [LinearOrder σ]
    (j : σ) (a b : ℕ) (hba : b ≤ a)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b)
    (m : ℕ)
    (i : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) m)
    (hi : (i.1 0).down = j) :
    StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) i.1
      ((Proj (MvPolynomial.homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (hi ▸ StandardCech.MvPolynomial.coordinateOpenCechIntersection_le
          (R := R) i.1 0)).op
        (FrameMapCoefficient.coefficient f
          (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
          (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame
            (R := R) j j a)
          (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame
            (R := R) j j b))) =
    PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (.of R), ⊤)
      (fun l => (i.1 l).down)
      (DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials
        (R := R) j (a - b)
        (NegativeTwistHomSections.MvPolynomial.coordinateNegativeTwistHomSection
          (R := R) j a b hba f)).val := by
  rw [coefficient_eq_chartCoefficient]
  exact chartCoefficient_on_intersection_of_eq j (a - b)
    (NegativeTwistHomSections.MvPolynomial.coordinateNegativeTwistHomSection
      (R := R) j a b hba f) m i hi

end SteinerGeometry.NegativeMapCoefficient
