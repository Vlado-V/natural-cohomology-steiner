import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MultiplicationCharacter.LineBundles
import SteinerGeometry.ConstantCharacterTrivial
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! The actual finite line decomposition of the multiplication pushforward. -/
noncomputable section
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

/-- Characters of the finite ordered multiplication kernel. -/
abbrev StructureCharacterIndex (g N : ℕ) :=
  ULift.{0} (Multiplicative (Fin (2 * g) → ZMod N)) →* ℂˣ

local instance multiplicationCharacterSplittingBiproducts (X : Scheme) :
    HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts
instance multiplicationCharacterSplittingFintype (g N : ℕ) [NeZero N] :
    Fintype (StructureCharacterIndex g N) := Fintype.ofFinite _

variable {g N : ℕ} [NeZero N]
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of ℂ))) (level : A.FullLevel N)

/-- The actual locally free rank-one character summands. -/
def multiplicationCharacterLineFamily (χ : StructureCharacterIndex g N) :
    Line.Bundles.LineBundle A.scheme.left :=
  A.multiplicationCharacterLineBundle level χ (Nat.cast_ne_zero.mpr (NeZero.ne N))

@[simp] theorem multiplicationCharacterLineFamily_sheaf (χ : StructureCharacterIndex g N) :
    (multiplicationCharacterLineFamily A level χ).sheaf =
      A.multiplicationCharacterSheaf level χ := rfl

/-- The Fourier projectors split the genuine structure-sheaf direct image
into actual line bundles, not merely into numerical character spaces. -/
def multiplicationStructureCharacterDecomposition :
    (Scheme.Modules.pushforward (A.multiplication N).left).obj
        (Line.Bundles.structureModule A.scheme.left) ≅
      ⨁ fun χ : StructureCharacterIndex g N => (multiplicationCharacterLineFamily A level χ).sheaf :=
  A.multiplicationCharacterDecomposition level (Nat.cast_ne_zero.mpr (NeZero.ne N))

/-- Every character line is actually trivialized by the same multiplication
cover, via its canonical comparison to the constant-torsor eigensheaf. -/
def multiplicationCharacterPullbackIso (χ : StructureCharacterIndex g N) :
    ((multiplicationCharacterLineFamily A level χ).pullback (A.multiplication N).left).sheaf ≅
      Line.Bundles.structureModule A.scheme.left := by
  let G := ULift.{0} (Multiplicative (Fin (2 * g) → ZMod N))
  let c := Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hG : (Fintype.card G : ℂ) ≠ 0 := TameCharacters.fullLevelCharacter_order_nonzero ℂ g N hN
  have : HasEnoughRootsOfUnity ℂ (Monoid.exponent G) :=
    TameCharacters.tameFiniteAbelian_hasEnoughRoots ℂ G hG
  exact A.multiplicationCharacterComparisonIso level χ hN ≪≫
    ConstantCharacterTrivial.constantCharacterSheafIso c G χ hG

/-- The number of actual character-line summands is the degree of multiplication. -/
theorem structureCharacterIndex_card : Nat.card (StructureCharacterIndex g N) = N ^ (2 * g) :=
  TameCharacters.fullLevelCharacter_card ℂ g N (Nat.cast_ne_zero.mpr (NeZero.ne N))

theorem doublingStructureCharacterIndex_card : Nat.card (StructureCharacterIndex 1 2) = 4 := by
  simpa using structureCharacterIndex_card (g := 1) (N := 2)

end SteinerGeometry
