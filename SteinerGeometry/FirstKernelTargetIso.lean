module

public import SteinerGeometry.SymmetricKernelChart
public import SteinerGeometry.ContractionTargetIso

set_option backward.privateInPublic true
@[expose] public section

/-! A frame on the evaluation target transports the actual first-kernel splitting. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
variable {X : Scheme.{u}}
local instance firstKernelTargetIsoBiproducts : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts

theorem structureEvaluation_postcompose {n : ℕ} {N N' : X.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N)) (q : N ⟶ N') :
    structureEvaluation e ≫ q = structureEvaluation (fun i => e i ≫ q) := by
  apply biproduct.hom_ext'
  intro i
  simp [structureEvaluation]

/-- Changing the target frame preserves the first evaluation kernel. -/
def firstKernelTargetIso {n : ℕ} {N N' : X.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N)) (q : N ≅ N') :
    kernel (structureEvaluation e) ≅ kernel (structureEvaluation (fun i => e i ≫ q.hom)) :=
  kernel.mapIso _ _ (Iso.refl _) q (by simpa using structureEvaluation_postcompose e q.hom)

@[simp, reassoc] theorem firstKernelTargetIso_hom_ι {n : ℕ} {N N' : X.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N)) (q : N ≅ N') :
    (firstKernelTargetIso e q).hom ≫ kernel.ι (structureEvaluation (fun i => e i ≫ q.hom)) =
      kernel.ι (structureEvaluation e) := by
  simp [firstKernelTargetIso]

/-- Canonical kernel columns are independent of the frame of the evaluation target. -/
theorem firstKernelColumns_targetIso {n : ℕ} {N N' : X.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N)) (q : N ≅ N')
    (L : Fin n → Line.Bundles.LineBundle X)
    (E : (⨁ fun j => (L j).sheaf) ≅ kernel (structureEvaluation e)) (i : Fin n) :
    firstKernelColumns (fun j => e j ≫ q.hom) L (E ≪≫ firstKernelTargetIso e q) i =
      firstKernelColumns e L E i := by
  simp only [firstKernelColumns, Iso.trans_hom, Category.assoc, firstKernelTargetIso_hom_ι_assoc]

end SteinerGeometry
