module

public import SteinerGeometry.PresentationEulerCurve
public import SteinerGeometry.CurveCohomologyFinite
public import SteinerGeometry.CurvePresentation
public import SteinerGeometry.LinePushforwardFinite

set_option backward.privateInPublic true
@[expose] public section

/-! Automatic finite-cohomology Euler additivity for genuine curve presentations. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.PresentationEuler
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology
local instance presentationEulerFiniteBiproducts (X : Scheme) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The actual finite-free bundle has rank times the structure Euler characteristic. -/
theorem freeSheaf_euler {X : Scheme} [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p]
    (hd : topologicalKrullDim X ≤ 1) (m : ℕ) :
    χ p (DualEvaluation.freeSheaf (X := X) m) =
      (m : ℤ) * χ p (Line.Bundles.structureModule X) := by
  have : (Line.Bundles.structureModule X).IsQuasicoherent :=
    (Line.Bundles.LineBundle.trivial X).isQuasicoherent
  have : (Line.Bundles.structureModule X).IsFiniteType :=
    (Line.Bundles.LineBundle.trivial X).isFiniteType
  exact freeSheaf_curve_euler p hd m

/-- The six-term cohomology sequence gives the relation-line Euler value. -/
theorem relation_euler {X : Scheme} [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p]
    (hd : topologicalKrullDim X ≤ 1) {m : ℕ}
    (R : Line.Bundles.LineBundle X) {Q : X.Modules}
    [Q.IsQuasicoherent] [Q.IsFiniteType]
    (i : R.sheaf ⟶ DualEvaluation.freeSheaf m)
    (s : DualEvaluation.freeSheaf m ⟶ Q) (w : i ≫ s = 0)
    (hS : (ShortComplex.mk i s w).ShortExact)
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (r : ℤ) (hQ : χ p Q = r) : χ p R.sheaf = -r := by
  have : (Line.Bundles.structureModule X).IsQuasicoherent :=
    (Line.Bundles.LineBundle.trivial X).isQuasicoherent
  have : (Line.Bundles.structureModule X).IsFiniteType :=
    (Line.Bundles.LineBundle.trivial X).isFiniteType
  have : R.sheaf.IsQuasicoherent := R.isQuasicoherent
  have : R.sheaf.IsFiniteType := R.isFiniteType
  exact relation_euler_of_curve_finite p hd R i s w hS hO r hQ

end SteinerGeometry.PresentationEuler

namespace SteinerGeometry.CyclicEtaleIsogeny
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology
local instance cyclicPresentationEulerFiniteBiproducts (X : Scheme) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts
variable {D : EllipticScheme} {n : ℕ} (q : CyclicEtaleIsogeny D n)
    [IsNoetherian q.target.scheme.left]
    [CurveCohomologyFinite q.target.scheme.hom]

/-- The relation line in an actual presentation has the negative source Euler value. -/
theorem presentationRelation_euler
    (hd : topologicalKrullDim q.target.scheme.left ≤ 1)
    (hO : χ q.target.scheme.hom (Line.Bundles.structureModule q.target.scheme.left) = 0)
    (A : Line.Bundles.LineBundle D.scheme.left)
    (P : CurvePresentationData (q.linePushforward A) n) :
    χ q.target.scheme.hom P.relationLine.sheaf = -χ D.scheme.hom A.sheaf := by
  have : A.sheaf.IsQuasicoherent := A.isQuasicoherent
  have : (q.linePushforward A).IsQuasicoherent :=
    OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom q.map.hom.left
  have : (q.linePushforward A).IsFiniteType := linePushforward_isFiniteType q.map.hom.left A
  exact PresentationEuler.relation_euler q.target.scheme.hom hd P.relationLine
    P.inclusion P.quotient P.zero P.exact hO _ (q.linePushforward_euler A)

end SteinerGeometry.CyclicEtaleIsogeny
