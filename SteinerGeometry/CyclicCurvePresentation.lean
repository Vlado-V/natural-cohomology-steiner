import SteinerGeometry.CurvePresentation
import SteinerGeometry.CyclicLineFrames
import SteinerGeometry.LinePushforwardFinite
import SteinerGeometry.LinePushforwardSections
import SteinerGeometry.CyclicComplexBase

/-! A rank-plus-one presentation of the actual cyclic-isogeny direct image. -/
noncomputable section
namespace SteinerGeometry.CyclicEtaleIsogeny
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {D : EllipticScheme} {n : ℕ} [NeZero n]
    (q : CyclicEtaleIsogeny D n)
    [IsIntegral q.target.scheme.left] [IsNoetherian q.target.scheme.left]

theorem exists_curvePresentation (A : Line.Bundles.LineBundle D.scheme.left)
    (hd : topologicalKrullDim q.target.scheme.left ≤ 1)
    (hgenerated : ∀ a : CurveRationalPoint q.target.scheme.hom,
      Function.Surjective (curveSectionEvaluation q.target.scheme.hom (q.linePushforward A) a.val)) :
    Nonempty (CurvePresentationData (q.linePushforward A) n) := by
  haveI : (q.linePushforward A).IsQuasicoherent :=
    OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom q.map.hom.left
  haveI : (q.linePushforward A).IsFiniteType :=
    SteinerGeometry.linePushforward_isFiniteType q.map.hom.left A
  refine exists_curvePresentationData q.target.scheme.hom hd (q.linePushforward A) n
    (NeZero.pos n) ?_ hgenerated ?_
  · intro a
    exact q.linePushforward_rankFrames A q.target.scheme.hom a.val a.property
  · intro U hU
    exact (linePushforward_affineRestriction_finite_projective q.map.hom.left A U hU).2

end SteinerGeometry.CyclicEtaleIsogeny
