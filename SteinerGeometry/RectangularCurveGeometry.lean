import SteinerGeometry.RectangularModel
import SteinerGeometry.PointLineBundle
import SteinerGeometry.CurveRationalPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.FramePresentation
import OAI.AlgebraicGeometry.SheafCohomology.DimensionBound

namespace SteinerGeometry

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

namespace RectangularModel

variable {k : ℕ} [NeZero k] (B : RectangularModel k)

/-- The algebraic rectangular torus is Noetherian because it is proper over a field. -/
instance rectangularGeometry_noetherian : IsNoetherian B.elliptic.scheme.left := by
  let : IsLocallyNoetherian B.elliptic.scheme.left :=
    LocallyOfFiniteType.isLocallyNoetherian B.elliptic.scheme.hom
  let : CompactSpace B.elliptic.scheme.left :=
    (quasiCompact_iff_compactSpace B.elliptic.scheme.hom).mp inferInstance
  exact ⟨⟩

/-- Properness of the algebraic model also gives separatedness of its carrier. -/
instance rectangularGeometry_separated : B.elliptic.scheme.left.IsSeparated := by
  constructor
  rw [← terminal.comp_from B.elliptic.scheme.hom]
  infer_instance

/-- The analytic dimension calculation gives an actual bound on Zariski dimension. -/
theorem topologicalKrullDim_le_one : topologicalKrullDim B.elliptic.scheme.left ≤ 1 := by
  have ht := OAI.AlgebraicGeometry.SheafCohomology.DimensionBound.Projective.topologicalKrullDim_le_schemeTranscendenceDimension B.elliptic.scheme.hom
  have hd : OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension B.elliptic.scheme.hom = 1 := by
    rw [OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension]
    exact B.dimension_one
  simpa only [hd, Nat.cast_one] using ht

/-- The identity of the algebraic group is an actual rational point. -/
def identityPoint : Spec (.of ℂ) ⟶ B.elliptic.scheme.left :=
  (1 : Over.mk (𝟙 complexBase) ⟶ B.elliptic.scheme).left

@[reassoc (attr := simp)]
theorem identityPoint_over : B.identityPoint ≫ B.elliptic.scheme.hom = 𝟙 _ :=
  (1 : Over.mk (𝟙 complexBase) ⟶ B.elliptic.scheme).w

/-- The ideal of the identity point is an invertible sheaf on the genuine smooth curve. -/
def identityIdealLine : Line.Bundles.LineBundle B.elliptic.scheme.left :=
  rationalPointIdealLineBundle B.elliptic.scheme.hom B.identityPoint B.identityPoint_over

/-- The reciprocal point ideal is the standard effective point line bundle. -/
def identityPointLine : Line.Bundles.LineBundle B.elliptic.scheme.left :=
  B.identityIdealLine.reciprocalFrameBundle

/-- Algebraic group points agree with rational sections of the structure map. -/
def rationalPointEquiv :
    (Over.mk (𝟙 complexBase) ⟶ B.elliptic.scheme) ≃
      CurveRationalPoint B.elliptic.scheme.hom where
  toFun a := ⟨a.left, a.w⟩
  invFun a := Over.homMk a.val a.property
  left_inv a := by ext; rfl
  right_inv a := rfl

instance rectangularGeometry_rationalPointsInfinite :
    Infinite (CurveRationalPoint B.elliptic.scheme.hom) :=
  Infinite.of_injective B.rationalPointEquiv B.rationalPointEquiv.injective

end RectangularModel
end
end SteinerGeometry
