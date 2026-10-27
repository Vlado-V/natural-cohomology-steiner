import SteinerGeometry.PullbackDualKernel
import SteinerGeometry.LinePushforwardSections

/-! The first-kernel splitting for a genuine cyclic-isogeny presentation. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.CyclicEtaleIsogeny
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open OAI.AlgebraicGeometry.Picard.Homomorphisms

local instance cyclicKernelSplittingBiproducts (X : Scheme) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {S : Scheme} {D : Abelian.Schemes.AbelianScheme 1 S} {n : ℕ}
    (q : CyclicEtaleIsogeny D n) [NeZero n]
    [IsLocallyNoetherian q.target.scheme.left]

/-- Pullback of the actual dual-evaluation kernel splits into the duals of
    the translated line bundle. All local splitting and dual base change
    are proved from the given genuine short exact presentation. -/
def evaluationKernelPullbackSplitting {m : ℕ}
    (A : Line.Bundles.LineBundle D.scheme.left)
    (R : Line.Bundles.LineBundle q.target.scheme.left)
    (i : R.sheaf ⟶ DualEvaluation.freeSheaf m)
    (p : DualEvaluation.freeSheaf m ⟶ q.linePushforward A) (w : i ≫ p = 0)
    (hS : (ShortComplex.mk i p w).ShortExact) :
    (Scheme.Modules.pullback q.map.hom.left).obj (kernel (DualEvaluation.evaluation R i)) ≅
      ∐ (fun j : Multiplicative (ZMod n) =>
        (LineBundleDual.Construction.lineBundleDual (q.translatedLineBundle A j)).sheaf) :=
  q.presentationKernelSplitting_of_affine_presentation A R i p w hS
    (fun U : q.target.scheme.left.affineOpens => U.1)
    (iSup_affineOpens_eq_top q.target.scheme.left)
    (fun U => U.2)
    (fun U => (linePushforward_affineRestriction_finite_projective q.map.hom.left A U.1 U.2).2)

end SteinerGeometry.CyclicEtaleIsogeny
