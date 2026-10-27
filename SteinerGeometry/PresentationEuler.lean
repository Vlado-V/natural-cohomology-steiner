import SteinerGeometry.PresentationEulerFinite
import SteinerGeometry.EulerDegree
import SteinerGeometry.MonomialLineDual
import SteinerGeometry.PointEuler

/-! Euler degrees of the actual rank-plus-one presentation, without a determinant formula. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.PresentationEuler
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open OAI.AlgebraicGeometry.Picard.Homomorphisms
open EllipticCohomology

local instance presentationEulerBiproducts (X : Scheme) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Native line duality and tensor additivity discharge the two target Euler values. -/
theorem relationDual_tensor_euler {X : Scheme} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [IsProper p] [CurveCohomologyFinite p]
    (hd : topologicalKrullDim X ≤ 1)
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (H : Line.Bundles.LineBundle X) (hH : 0 < χ p H.sheaf) {m : ℕ}
    (R B : Line.Bundles.LineBundle X) {Q : X.Modules}
    [Q.IsQuasicoherent] [Q.IsFiniteType]
    (i : R.sheaf ⟶ DualEvaluation.freeSheaf m)
    (s : DualEvaluation.freeSheaf m ⟶ Q) (w : i ≫ s = 0)
    (hS : (ShortComplex.mk i s w).ShortExact)
    (r t : ℤ) (hQ : χ p Q = r) (hB : χ p B.sheaf = t) :
    χ p (DualEvaluation.targetLine R).sheaf = r ∧
      χ p ((DualEvaluation.targetLine R).tensor B).sheaf = r + t := by
  have : (Line.Bundles.structureModule X).IsQuasicoherent :=
    (Line.Bundles.LineBundle.trivial X).isQuasicoherent
  have : (Line.Bundles.structureModule X).IsFiniteType :=
    (Line.Bundles.LineBundle.trivial X).isFiniteType
  have : R.sheaf.IsQuasicoherent := R.isQuasicoherent
  have : R.sheaf.IsFiniteType := R.isFiniteType
  exact relationDual_tensor_euler_of_laws p hd R B i s w hS hO
    (fun L => EulerDegree.inversePair_euler p hd hO H hH L
      (LineBundleDual.Construction.lineBundleDual L) (lineBundleDual_primal_pairing L).some)
    (EulerDegree.tensor_euler_add p hd hO H hH) r t hQ hB

end SteinerGeometry.PresentationEuler

namespace SteinerGeometry.CyclicEtaleIsogeny
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology

local instance cyclicPresentationEulerBiproducts (X : Scheme) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {D : EllipticScheme} {n : ℕ} (q : CyclicEtaleIsogeny D n)
    [IsIntegral q.target.scheme.left] [IsNoetherian q.target.scheme.left]
    [CurveCohomologyFinite q.target.scheme.hom]

/-- The paper's two section-space Euler values follow from the actual
presentation. A positive reference is constructed from the identity point. -/
theorem presentationTarget_euler
    (hd : topologicalKrullDim q.target.scheme.left ≤ 1)
    (hO : χ q.target.scheme.hom (Line.Bundles.structureModule q.target.scheme.left) = 0)
    (A : Line.Bundles.LineBundle D.scheme.left)
    (P : CurvePresentationData (q.linePushforward A) n)
    (B : Line.Bundles.LineBundle q.target.scheme.left)
    (r t : ℤ) (hA : χ D.scheme.hom A.sheaf = r)
    (hB : χ q.target.scheme.hom B.sheaf = t) :
    χ q.target.scheme.hom (DualEvaluation.targetLine P.relationLine).sheaf = r ∧
      χ q.target.scheme.hom ((DualEvaluation.targetLine P.relationLine).tensor B).sheaf = r + t := by
  have : A.sheaf.IsQuasicoherent := A.isQuasicoherent
  have : (q.linePushforward A).IsQuasicoherent :=
    OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom q.map.hom.left
  have : (q.linePushforward A).IsFiniteType := linePushforward_isFiniteType q.map.hom.left A
  have : IsProper q.target.scheme.hom := q.target.proper
  have : SmoothOfRelativeDimension 1 q.target.scheme.hom := q.target.smoothDimension
  let a : Spec (.of ℂ) ⟶ q.target.scheme.left := η[q.target.scheme].left
  have ha : a ≫ q.target.scheme.hom = 𝟙 _ := η[q.target.scheme].w
  let H := (rationalPointIdealLineBundle q.target.scheme.hom a ha).reciprocalFrameBundle
  have hH : 0 < χ q.target.scheme.hom H.sheaf := by
    have he := PointEuler.rationalPointLine_euler q.target.scheme.hom hd a ha hO
    change 0 < χ q.target.scheme.hom
      (rationalPointIdealLineBundle q.target.scheme.hom a ha).reciprocalFrameBundle.sheaf
    rw [he]
    omega
  exact PresentationEuler.relationDual_tensor_euler q.target.scheme.hom hd hO H hH
    P.relationLine B P.inclusion P.quotient P.zero P.exact r t
    ((q.linePushforward_euler A).trans hA) hB

end SteinerGeometry.CyclicEtaleIsogeny
