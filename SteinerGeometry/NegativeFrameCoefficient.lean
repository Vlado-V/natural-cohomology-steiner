import SteinerGeometry.LocalTensorPowerFrame
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeChartCoordinates
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenFrames
import OAI.AlgebraicGeometry.SheafCohomology.Projective.UnitFrameSection

/-! The normalized negative-chart functional is the canonical twist-frame coefficient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SteinerGeometry.NegativeFrameCoefficient
open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective
open LocalTensorFrames
universe u
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
local instance negativeFrameCoefficient_monoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

theorem coefficient_overTrivializationSection_one {X : Scheme.{u}}
    (M : X.Modules) (U : X.affineOpens)
    (e : M.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1)) :
    coefficient M U (FrameSections.restrictTrivializationOfOverIso M U.1 e)
      (FrameSections.overTrivializationSection M U.1 e 1) = 1 := by
  rw [coefficient_restrictTrivializationOfOverIso,
    FrameSections.overTrivializationSection_coefficient]
  simp only [FrameSections.affineOpenTopSection, map_one]

/-- Every local tensor-power generator has coefficient one in the recursively
constructed canonical negative-twist frame. -/
theorem generator_coefficient (j : σ) (n : ℕ) :
    coefficient (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n)
      ⟨MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j,
        MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen j⟩
      (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivialization (R := R) j j n)
      (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection
        (R := R) j n) = 1 := by
  let U : (Proj (MvPolynomial.homogeneousSubmodule σ R)).affineOpens :=
    ⟨MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j,
      MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen j⟩
  let I := IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)
  let e := (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization
    (R := R) j j).symm
  let q := FrameSections.overTrivializationSection I U.1
    (HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplaneIdealOverTrivialization
      (R := R) j j) 1
  have hq : coefficient I U e q = 1 := by
    have h := coefficient_overTrivializationSection_one I U
      (HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplaneIdealOverTrivialization
        (R := R) j j)
    change coefficient I U (FrameSections.restrictTrivializationOfOverIso I U.1
      (Invertible.Scheme.Modules.overTrivializationOfRestrictIso I U.1 e)) q = 1 at h
    rwa [OpenFrames.restrictTrivializationOfOverTrivializationOfRestrictIso] at h
  change coefficient (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n)
    U (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivialization (R := R) j j n)
    (LocalPowerSections.MvPolynomial.coordinateHyperplaneIdealLocalTensorPower j U.1 q n) = 1
  have h := LocalTensorPowerFrame.idealLocalTensorPower_coefficient j U e q n
  rw [hq, one_pow] at h
  exact h

/-- The same normalization in the original ambient over-site frame. -/
theorem generator_overCoefficient (j : σ) (n : ℕ) :
    (RankOneMapCoordinates.overFrameSectionEquiv
      (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n)
      (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
      (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame
        (R := R) j j n)).symm
      (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection
        (R := R) j n) = 1 := by
  let U : (Proj (MvPolynomial.homogeneousSubmodule σ R)).affineOpens :=
    ⟨MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j,
      MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen j⟩
  let M := TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n
  let e := NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame
    (R := R) j j n
  let s := DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection
    (R := R) j n
  have h := coefficient_restrictTrivializationOfOverIso M U e s
  change coefficient M U (FrameSections.restrictTrivializationOfOverIso M U.1
      (Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U.1
        (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivialization
          (R := R) j j n))) s = _ at h
  rw [OpenFrames.restrictTrivializationOfOverTrivializationOfRestrictIso] at h
  have hh : FrameSections.affineOpenTopSection U (e.hom.val.app (op (Over.mk (𝟙 U.1))) s) = 1 :=
    h.symm.trans (generator_coefficient j n)
  have hh' := congrArg (FrameSections.affineOpenAmbientSection U) hh
  rw [FrameSections.affineOpenAmbientSection_topSection] at hh'
  change e.hom.val.app (op (Over.mk (𝟙 U.1))) s =
    (show Γ(Proj (MvPolynomial.homogeneousSubmodule σ R), U.1) from 1)
  simpa only [FrameSections.affineOpenAmbientSection, map_one] using hh'

/-- The native cancellation-normalized functional equals the actual canonical
negative-twist frame coordinate, on every local section. -/
theorem negativeChartCoefficient_eq_overCoefficient (j : σ) (n : ℕ)
    (x : Γ(TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n,
      MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)) :
    NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneNegativeChartCoefficient j n x =
      (RankOneMapCoordinates.overFrameSectionEquiv
        (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n)
        (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
        (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame
          (R := R) j j n)).symm x := by
  let E := RankOneMapCoordinates.overFrameSectionEquiv
    (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n)
    (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
    (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame (R := R) j j n)
  symm
  calc
    E.symm x = E.symm
        (NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneNegativeChartCoefficient j n x •
          DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection
            (R := R) j n) :=
      congrArg E.symm
        (NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneIdealChartPowerSection_generates j n x)
    _ = _ := E.symm.map_smul _ _
    _ = _ := by rw [generator_overCoefficient]; exact mul_one _

end SteinerGeometry.NegativeFrameCoefficient
