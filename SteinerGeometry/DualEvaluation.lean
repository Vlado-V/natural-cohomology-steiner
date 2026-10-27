module

public import SteinerGeometry.SheafDual

set_option backward.privateInPublic true
@[expose] public section

/-! The evaluation map obtained from an actual line subbundle of a free sheaf. -/
noncomputable section
namespace SteinerGeometry.DualEvaluation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.Picard.Homomorphisms
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open SheafDual
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}}

local instance dualEvaluationBiproducts : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

abbrev freeSheaf (m : ℕ) : X.Modules :=
  ⨁ fun _ : Fin m => Line.Bundles.structureModule X

def freeDualIso (m : ℕ) : dual (freeSheaf (X := X) m) ≅ freeSheaf (X := X) m :=
  dualBiproductIso _ ≪≫ biproduct.mapIso (fun _ =>
    InternalHomUnit.Construction.internalHomUnitIso (Line.Bundles.structureModule X))

def targetLine (R : Line.Bundles.LineBundle X) : Line.Bundles.LineBundle X :=
  LineBundleDual.Construction.lineBundleDual R

def evaluation {m : ℕ} (R : Line.Bundles.LineBundle X)
    (i : R.sheaf ⟶ freeSheaf m) : freeSheaf m ⟶ (targetLine R).sheaf :=
  (freeDualIso m).inv ≫ dualMap i

def kernelIso {m : ℕ} (R : Line.Bundles.LineBundle X)
    (i : R.sheaf ⟶ freeSheaf m) : kernel (evaluation R i) ≅ kernel (dualMap i) :=
  kernel.mapIso _ _ (freeDualIso m).symm (Iso.refl _) (by
    change ((freeDualIso m).inv ≫ dualMap i) ≫ 𝟙 _ = (freeDualIso m).inv ≫ dualMap i
    exact Category.comp_id _)

theorem evaluation_splitEpi_of_retraction {m : ℕ} (R : Line.Bundles.LineBundle X)
    (i : R.sheaf ⟶ freeSheaf m) (r : freeSheaf m ⟶ R.sheaf)
    (hi : i ≫ r = 𝟙 R.sheaf) : IsSplitEpi (evaluation R i) := by
  refine ⟨⟨dualMap r ≫ (freeDualIso m).hom, ?_⟩⟩
  change (dualMap r ≫ (freeDualIso m).hom) ≫ (freeDualIso m).inv ≫ dualMap i = 𝟙 (dual R.sheaf)
  simp only [evaluation, Category.assoc, Iso.hom_inv_id_assoc, ← dualMap_comp, hi, dualMap_id]

end SteinerGeometry.DualEvaluation
