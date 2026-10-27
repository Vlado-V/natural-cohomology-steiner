import SteinerGeometry.DualEvaluation
import SteinerGeometry.DualRestriction
import SteinerGeometry.TildeFiniteProjective

/-! The actual internal-Hom dual preserves finite rank on every open frame. -/
noncomputable section
namespace SteinerGeometry.FiniteDualFrames
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.Picard.Homomorphisms
universe u
local instance finiteDualFrames_biproducts (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

def freeToBiproduct (X : Scheme.{u}) (r : ℕ) :
    (show X.Modules from SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))) ≅
      DualEvaluation.freeSheaf (X := X) r := by
  let F : Fin r → X.Modules := fun _ => SheafOfModules.unit X.ringCatSheaf
  letI : HasBiproduct F := HasBiproduct.of_hasCoproduct F
  exact Sigma.reindex Equiv.ulift F ≪≫ (biproduct.isoCoproduct F).symm

def dualFrame {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (r : ℕ)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))) :
    (Scheme.Modules.pullback U.ι).obj (SheafDual.dual M) ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r)) :=
  ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app (SheafDual.dual M)).symm ≪≫
    InternalHomRestriction.Construction.moduleInternalHomRestrictIso U.ι M
      (OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) ≪≫
    InternalHomMaps.Construction.moduleInternalHomCongr
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫ e ≪≫ freeToBiproduct U.toScheme r)
      (Scheme.Modules.restrictUnitIso U.ι) ≪≫
    DualEvaluation.freeDualIso r ≪≫ (freeToBiproduct U.toScheme r).symm

end SteinerGeometry.FiniteDualFrames
