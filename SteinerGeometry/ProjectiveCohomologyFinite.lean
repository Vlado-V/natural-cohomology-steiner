import SteinerGeometry.CurveCohomologyFinite
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ProjectiveZariskiFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.TwistingSectionsFinite

/-! Coherent cohomology finiteness from an explicit projective presentation. -/
noncomputable section
namespace SteinerGeometry
open CategoryTheory AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology

/-- All actual coherent cohomology spaces are finite-dimensional on a scheme
with a specified closed projective embedding. -/
theorem projectivePresentation_cohomology_finite
    {X : Over (Spec (.of ℂ))}
    (P : Projective.ProjectivePresentations.ProjectivePresentation X)
    (M : X.left.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (j : ℕ) :
    Module.Finite ℂ (H X.hom M j) :=
  Closed.ProjectiveZariskiFiniteness.ClosedProjectiveEmbedding.cohomology_finite
    (RelativeProjective.TwistingSectionsFinite.relativeEmbeddingAffineMap P.embedding) M j

/-- An explicit closed projective embedding supplies the cohomology-finiteness
class used by the curve Euler calculation. -/
theorem curveCohomologyFiniteOfProjectivePresentation
    {X : Over (Spec (.of ℂ))}
    (P : Projective.ProjectivePresentations.ProjectivePresentation X) :
    CurveCohomologyFinite X.hom where
  finite M _ _ j := projectivePresentation_cohomology_finite P M j

end SteinerGeometry
