import SteinerGeometry.RectangularCurveGeometry
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange

/-! The constructed rectangular curve has a genuine closed projective embedding. -/
noncomputable section
namespace SteinerGeometry.RectangularModel
open CategoryTheory AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

variable {k : ℕ} [NeZero k] (B : RectangularModel k)

/-- The absolute polynomial projective embedding, regarded over the actual base field. -/
def affineProjectiveEmbedding :
    B.elliptic.scheme ⟶ Projective.ProjectivePresentations.affineProjectiveSpace ℂ
      B.projective.ambientDimension :=
  Over.homMk B.projective.embedding B.projective.over_base

instance rectangularProjective_embedding_closed :
    IsClosedImmersion B.affineProjectiveEmbedding.left :=
  B.projective.closedImmersion

/-- The same embedding in the native relative projective-space convention. -/
def hilbertProjective : Projective.ProjectivePresentations.ProjectivePresentation
    B.elliptic.scheme where
  dimension := B.projective.ambientDimension
  embedding := B.affineProjectiveEmbedding ≫
    (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of ℂ)
      B.projective.ambientDimension).inv
  closedImmersion := by
    let e := Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of ℂ)
      B.projective.ambientDimension
    let : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
    exact inferInstanceAs (IsClosedImmersion (B.affineProjectiveEmbedding.left ≫ e.inv.left))

end SteinerGeometry.RectangularModel
