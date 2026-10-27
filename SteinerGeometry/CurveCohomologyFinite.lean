import SteinerGeometry.NativeCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Quasicoherence

/-! A finiteness property to be supplied by an actual projective embedding. -/
namespace SteinerGeometry
open AlgebraicGeometry
open EllipticCohomology

/-- Every coherent module on this curve has finite-dimensional actual cohomology.
The projective-embedding construction supplies the instance used below. -/
class CurveCohomologyFinite {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) : Prop where
  finite (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (q : ℕ) :
    Module.Finite ℂ (H p M q)

attribute [instance] CurveCohomologyFinite.finite
end SteinerGeometry
