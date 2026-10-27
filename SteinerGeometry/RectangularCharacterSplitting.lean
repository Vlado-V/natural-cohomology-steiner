import SteinerGeometry.MultiplicationCharacterSplitting
import SteinerGeometry.RectangularFullLevel

/-! Four actual character lines for the rectangular curve's self-[2] map. -/
noncomputable section
namespace SteinerGeometry.RectangularModel
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

local instance rectangularCharacterSplittingBiproducts (X : Scheme) :
    HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts
variable {k : ℕ} [NeZero k] (B : RectangularModel k)

/-- The actual character line attached to one of the four characters. -/
def doublingCharacterLine (χ : StructureCharacterIndex 1 2) :
    Line.Bundles.LineBundle B.elliptic.scheme.left :=
  multiplicationCharacterLineFamily B.elliptic B.fullLevelTwo χ

/-- The genuine self-cover direct image is the sum of these four lines. -/
def doublingStructureCharacterDecomposition :
    (Scheme.Modules.pushforward B.doubling.hom.left).obj
        (Line.Bundles.structureModule B.elliptic.scheme.left) ≅
      ⨁ fun χ : StructureCharacterIndex 1 2 => (B.doublingCharacterLine χ).sheaf :=
  multiplicationStructureCharacterDecomposition B.elliptic B.fullLevelTwo

/-- Pullback by the same self-cover trivializes every actual character line. -/
def doublingCharacterPullbackIso (χ : StructureCharacterIndex 1 2) :
    ((B.doublingCharacterLine χ).pullback B.doubling.hom.left).sheaf ≅
      Line.Bundles.structureModule B.elliptic.scheme.left :=
  multiplicationCharacterPullbackIso B.elliptic B.fullLevelTwo χ

end SteinerGeometry.RectangularModel
