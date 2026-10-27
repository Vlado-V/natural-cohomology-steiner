import SteinerGeometry.RectangularProjective
import SteinerGeometry.ProjectiveCohomologyFinite
import SteinerGeometry.RectangularCharacterSplitting
import SteinerGeometry.CurveSelfCoverTorsion
import SteinerGeometry.PointEuler
import SteinerGeometry.FinitePicardAvoidance

/-! The actual rectangular elliptic curve has structure Euler characteristic zero. -/
noncomputable section
namespace SteinerGeometry.RectangularModel
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology

variable {k : ℕ} [NeZero k] (B : RectangularModel k)

/-- The chosen closed projective embedding gives finiteness of genuine coherent cohomology. -/
instance rectangularGenus_cohomologyFinite : CurveCohomologyFinite B.elliptic.scheme.hom :=
  curveCohomologyFiniteOfProjectivePresentation B.hilbertProjective

/-- The invertible ideal of the identity produces a positive Euler-degree reference
without first assuming the genus. -/
theorem identityPointLine_euler_succ :
    χ B.elliptic.scheme.hom B.identityPointLine.sheaf =
      χ B.elliptic.scheme.hom (Line.Bundles.structureModule B.elliptic.scheme.left) + 1 :=
  PointEuler.rationalPointLine_euler_general B.elliptic.scheme.hom
    B.topologicalKrullDim_le_one B.identityPoint B.identityPoint_over

/-- The finite flat self-cover has finite kernel on genuine line-bundle classes. -/
theorem doubling_pullbackClass_kernel_finite :
    Finite (Line.Bundles.LineBundle.pullbackClassMonoidHom B.doubling.hom.left).ker :=
  FinitePicardAvoidance.finite_lineKernel_of_finite_flat
    B.doubling.hom

/-- The four character lines of multiplication by two force χ(O)=0.  The proof
uses the actual self-cover, its actual sheaf decomposition, and the point line. -/
theorem structure_euler_zero :
    χ B.elliptic.scheme.hom (Line.Bundles.structureModule B.elliptic.scheme.left) = 0 := by
  obtain ⟨J, s, hs, hJ⟩ := PointEuler.exists_effective_positiveDegreeLine
    B.elliptic.scheme.hom B.topologicalKrullDim_le_one B.identityPoint B.identityPoint_over
  let : Finite (Line.Bundles.LineBundle.pullbackClassMonoidHom B.doubling.hom.left).ker :=
    B.doubling_pullbackClass_kernel_finite
  have hcard : Fintype.card (StructureCharacterIndex 1 2) ≠ 1 := by
    simpa only [Fintype.card_eq_nat_card, doublingStructureCharacterIndex_card] using
      (by decide : (4 : ℕ) ≠ 1)
  apply structure_euler_zero_of_trivialized_self_line_decomposition
    B.elliptic.scheme.hom B.topologicalKrullDim_le_one J s hs hJ
    B.doubling.hom.left B.doubling.hom.w hcard
    B.doublingCharacterLine B.doublingStructureCharacterDecomposition
  intro i
  exact ⟨B.doublingCharacterPullbackIso i⟩

end SteinerGeometry.RectangularModel
