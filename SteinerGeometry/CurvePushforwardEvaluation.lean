module

public import SteinerGeometry.CurveEvaluationDegree
public import SteinerGeometry.CurvePointEvaluation
public import SteinerGeometry.CyclicLineFrames
public import SteinerGeometry.LinePushforwardFinite
public import SteinerGeometry.CurveGeneratorsEpi

set_option backward.privateInPublic true
@[expose] public section

/-! The actual direct image admits rank-plus-one global generators when its
source line has degree larger than the covering degree. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.MonoidalCategory
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology
open scoped CategoryTheory.MonObj

namespace CyclicEtaleIsogeny

variable {D : EllipticScheme} {n : ℕ} [NeZero n] (q : CyclicEtaleIsogeny D n)
    [CurveCohomologyFinite D.scheme.hom] [CurveCohomologyFinite q.target.scheme.hom]

/-- Every rational evaluation of the actual finite direct image is surjective
when the source line degree exceeds the covering degree. -/
theorem linePushforward_evaluation_surjective
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
    (a : CurveRationalPoint q.target.scheme.hom) :
    Function.Surjective (curveSectionEvaluation q.target.scheme.hom (q.linePushforward A) a.val) := by
  let y : 𝟙_ (Over complexBase) ⟶ q.target.scheme := Over.homMk a.val a.property
  have : (q.linePushforward A).IsQuasicoherent :=
    OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom
      q.map.hom.left
  apply pointEvaluation_surjective_of_pointIdeal_h1_zero q.target.scheme.hom a.val a.property
    (q.linePushforward A) (linePushforward_finiteFrames q.map.hom.left A)
  exact CurveEvaluationDegree.pushforward_pointIdeal_h1_zero q hd hOD P hP hPne hOC A hA y

/-- A single fixed family of n+1 genuine global sections generates the actual
rank-n finite direct image over the whole target curve. -/
theorem exists_linePushforward_generators
    [IsIntegral D.scheme.left] [IsNoetherian D.scheme.left]
    [IsIntegral q.target.scheme.left] [IsNoetherian q.target.scheme.left]
    [SmoothOfRelativeDimension 1 q.target.scheme.hom]
    (hdD : topologicalKrullDim D.scheme.left ≤ 1)
    (hdC : topologicalKrullDim q.target.scheme.left ≤ 1)
    (hOD : χ D.scheme.hom (Line.Bundles.structureModule D.scheme.left) = 0)
    (P : Line.Bundles.LineBundle D.scheme.left)
    (hP : χ D.scheme.hom P.sheaf = 0)
    (hPne : ¬ Nonempty (P.sheaf ≅ Line.Bundles.structureModule D.scheme.left))
    (hOC : χ q.target.scheme.hom (Line.Bundles.structureModule q.target.scheme.left) = 0)
    (A : Line.Bundles.LineBundle D.scheme.left)
    (hA : (n : ℤ) < χ D.scheme.hom A.sheaf) :
    ∃ s : Fin (n + 1) → (SheafOfModules.unit q.target.scheme.left.ringCatSheaf ⟶
      q.linePushforward A), Epi (Sigma.desc s) := by
  have : (q.linePushforward A).IsQuasicoherent :=
    OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom
      q.map.hom.left
  have : (q.linePushforward A).IsFiniteType :=
    linePushforward_isFiniteType q.map.hom.left A
  apply exists_curve_generator_epimorphism q.target.scheme.hom hdC
    (q.linePushforward A) n (Nat.pos_of_ne_zero (NeZero.ne n))
  · intro a
    exact q.linePushforward_rankFrames A q.target.scheme.hom a.val a.property
  · intro a
    exact q.linePushforward_evaluation_surjective hdD hOD P hP hPne hOC A hA a

end CyclicEtaleIsogeny
end SteinerGeometry
