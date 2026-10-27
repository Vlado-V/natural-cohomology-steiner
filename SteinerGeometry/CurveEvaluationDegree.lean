import SteinerGeometry.CyclicDegree
import SteinerGeometry.EvaluationCohomology
import SteinerGeometry.EllipticEulerCohomology

/-! # Positive degree after imposing a point condition

The kernel of evaluation of a finite direct image is controlled by the
actual point ideal upstairs. Its Euler characteristic is the degree of
the source line minus the degree of the cyclic cover.
-/

noncomputable section

namespace SteinerGeometry.CurveEvaluationDegree

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.MonoidalCategory
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology EulerDegree
open scoped CategoryTheory.MonObj

variable {D : EllipticScheme} {n : ℕ} [NeZero n] (q : CyclicEtaleIsogeny D n)
    [CurveCohomologyFinite D.scheme.hom] [CurveCohomologyFinite q.target.scheme.hom]

/-- Imposing one point condition downstairs subtracts the degree of the cover
from the Euler degree of the actual line upstairs. -/
theorem pointIdeal_twist_euler
    [IsIntegral D.scheme.left] [IsNoetherian D.scheme.left]
    [IsLocallyNoetherian q.target.scheme.left]
    [SmoothOfRelativeDimension 1 q.target.scheme.hom]
    (hd : topologicalKrullDim D.scheme.left ≤ 1)
    (hOC : χ q.target.scheme.hom (Line.Bundles.structureModule q.target.scheme.left) = 0)
    (hOD : χ D.scheme.hom (Line.Bundles.structureModule D.scheme.left) = 0)
    (A : Line.Bundles.LineBundle D.scheme.left)
    (hA : 0 < χ D.scheme.hom A.sheaf)
    (y : 𝟙_ (Over complexBase) ⟶ q.target.scheme) :
    χ D.scheme.hom
      (((rationalPointIdealLineBundle q.target.scheme.hom y.left y.w).pullback
        q.map.hom.left).tensor A).sheaf = χ D.scheme.hom A.sheaf - n := by
  let : IsProper D.scheme.hom := D.proper
  rw [tensor_euler_add D.scheme.hom hd hOD A hA,
    CyclicDegree.pulledPointIdeal_euler_at q y hd hOC hOD]
  omega

/-- The point-condition line has no H¹ as soon as the source line degree
strictly exceeds the degree of the cover. -/
theorem pointIdeal_twist_h1_zero
    [IsIntegral D.scheme.left] [IsNoetherian D.scheme.left]
    [IsLocallyNoetherian q.target.scheme.left]
    [SmoothOfRelativeDimension 1 q.target.scheme.hom]
    (hd : topologicalKrullDim D.scheme.left ≤ 1)
    (hOD : χ D.scheme.hom (Line.Bundles.structureModule D.scheme.left) = 0)
    (P : Line.Bundles.LineBundle D.scheme.left)
    (hP : χ D.scheme.hom P.sheaf = 0)
    (hPne : ¬ Nonempty (P.sheaf ≅ Line.Bundles.structureModule D.scheme.left))
    (hOC : χ q.target.scheme.hom (Line.Bundles.structureModule q.target.scheme.left) = 0)
    (A : Line.Bundles.LineBundle D.scheme.left)
    (hA : (n : ℤ) < χ D.scheme.hom A.sheaf)
    (y : 𝟙_ (Over complexBase) ⟶ q.target.scheme) :
    IsZero (H D.scheme.hom
      (((rationalPointIdealLineBundle q.target.scheme.hom y.left y.w).pullback
        q.map.hom.left).tensor A).sheaf 1) := by
  let : IsProper D.scheme.hom := D.proper
  apply positive_euler_h1_zero_of_reference D.scheme.hom hd hOD A (by omega) P hP hPne
  rw [pointIdeal_twist_euler q hd hOC hOD A (by omega) y]
  omega

/-- Projection formula transports that vanishing to the point-ideal twist
of the actual direct image. -/
theorem pushforward_pointIdeal_h1_zero
    [IsIntegral D.scheme.left] [IsNoetherian D.scheme.left]
    [IsLocallyNoetherian q.target.scheme.left]
    [SmoothOfRelativeDimension 1 q.target.scheme.hom]
    (hd : topologicalKrullDim D.scheme.left ≤ 1)
    (hOD : χ D.scheme.hom (Line.Bundles.structureModule D.scheme.left) = 0)
    (P : Line.Bundles.LineBundle D.scheme.left)
    (hP : χ D.scheme.hom P.sheaf = 0)
    (hPne : ¬ Nonempty (P.sheaf ≅ Line.Bundles.structureModule D.scheme.left))
    (hOC : χ q.target.scheme.hom (Line.Bundles.structureModule q.target.scheme.left) = 0)
    (A : Line.Bundles.LineBundle D.scheme.left)
    (hA : (n : ℤ) < χ D.scheme.hom A.sheaf)
    (y : 𝟙_ (Over complexBase) ⟶ q.target.scheme) :
    IsZero (H q.target.scheme.hom
      (Tensor.ProductSheaf.tensorModule
        (rationalPointIdealLineBundle q.target.scheme.hom y.left y.w).sheaf
        ((Scheme.Modules.pushforward q.map.hom.left).obj A.sheaf)) 1) := by
  let : IsProper q.target.scheme.hom := q.target.proper
  let : q.target.scheme.left.IsSeparated := ⟨by
    rw [← terminal.comp_from q.target.scheme.hom]
    infer_instance⟩
  have h1 := pointIdeal_twist_h1_zero q hd hOD P hP hPne hOC A hA y
  apply EvaluationCohomology.pushforward_line_tensor_h1_zero q.map.hom.left
    q.target.scheme.hom (rationalPointIdealLineBundle q.target.scheme.hom y.left y.w) A
  simpa only [q.map.hom.w] using h1

end SteinerGeometry.CurveEvaluationDegree
