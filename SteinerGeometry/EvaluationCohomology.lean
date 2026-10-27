module

public import SteinerGeometry.CohomologySections
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Quasicoherence
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardCohomologyFiniteness
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ProjectionFormula

set_option backward.privateInPublic true
@[expose] public section

noncomputable section
namespace SteinerGeometry.EvaluationCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology

/-- Projection formula and affine direct-image cohomology transport a
line-bundle H¹ vanishing upstairs to the point-ideal twist of its direct image. -/
theorem pushforward_line_tensor_h1_zero
    {X Y : Scheme.{0}} [X.IsSeparated] (q : Y ⟶ X) [IsAffineHom q]
    (p : X ⟶ Spec (.of ℂ)) (I : Line.Bundles.LineBundle X)
    (A : Line.Bundles.LineBundle Y)
    (h1 : IsZero (H (q ≫ p) ((I.pullback q).tensor A).sheaf 1)) :
    IsZero (H p (Tensor.ProductSheaf.tensorModule I.sheaf
      ((Scheme.Modules.pushforward q).obj A.sheaf)) 1) := by
  let _ : ((I.pullback q).tensor A).sheaf.IsQuasicoherent :=
    ((I.pullback q).tensor A).isQuasicoherent
  let e := LineBundle.ProjectionFormula.lineBundleProjectionFormulaIso q I A.sheaf
  let F := Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
    (Coefficient.ModulePresheaf.schemeCoefficientMap p) 1
  have hpush : IsZero (F.obj ((Scheme.Modules.pushforward q).obj
      ((I.pullback q).tensor A).sheaf)) :=
    h1.of_iso (Affine.PushforwardCohomologyFiniteness.affinePushforwardCohomologyIso
      q p ((I.pullback q).tensor A).sheaf 1).symm
  exact hpush.of_iso (F.mapIso e)

end SteinerGeometry.EvaluationCohomology
