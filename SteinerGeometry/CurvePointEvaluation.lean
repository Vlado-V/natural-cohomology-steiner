import SteinerGeometry.CohomologySections
import SteinerGeometry.PointTensorExact
import SteinerGeometry.CurveSectionEvaluation

/-! Point-ideal cohomology controls the actual rational evaluation map. -/
noncomputable section
namespace SteinerGeometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology

/-- Vanishing of the actual point-ideal twist implies surjectivity of the
canonical rational-point evaluation map. -/
theorem pointEvaluation_surjective_of_pointIdeal_h1_zero {X : Scheme.{0}}
    (p : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 p]
    (a : Spec (.of ℂ) ⟶ X) (ha : a ≫ p = 𝟙 _)
    (E : X.Modules) [E.IsQuasicoherent]
    (D : TildeFiniteProjective.FiniteGeometricFrameCover E)
    (h1 : IsZero (H p (Tensor.ProductSheaf.tensorModule
      (rationalPointIdealLineBundle p a ha).sheaf E) 1)) :
    Function.Surjective (curveSectionEvaluation p E a) := by
  exact EvaluationCohomology.evaluation_surjective_of_h1_zero p a E _
    (pointTensorInclusion a E) (pointTensorInclusion_unit_zero a E)
    (pointTensor_shortExact p a ha E D) h1

end SteinerGeometry
