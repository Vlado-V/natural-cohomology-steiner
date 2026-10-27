module

public import SteinerGeometry.LineDualPullback
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

set_option backward.privateInPublic true
@[expose] public section

/-! Dual base change on finite sums of line bundles and maps from a line. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SteinerGeometry.SheafDual
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
variable {X Y : Scheme.{u}}

local instance splitDualPullbackBiproducts (Z : Scheme.{u}) : HasFiniteBiproducts Z.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

@[reassoc]
theorem dualMap_projection_comp {I : Type} [Fintype I] (M : I → X.Modules) (i : I) :
    dualMap (biproduct.π M i) ≫ (dualBiproductIso M).hom =
      biproduct.ι (fun j => dual (M j)) i := by
  classical
  apply biproduct.hom_ext
  intro j
  simp only [Category.assoc, dualBiproductIso, biproduct.lift_π, ← dualMap_comp]
  by_cases hij : i = j
  · subst j
    simp
  · simp [biproduct.ι_π_ne _ (Ne.symm hij), hij]

@[reassoc]
theorem dualBiproductIso_inv_projection {I : Type} [Fintype I] (M : I → X.Modules) (i : I) :
    biproduct.ι (fun j => dual (M j)) i ≫ (dualBiproductIso M).inv =
      dualMap (biproduct.π M i) := by
  simp only [dualBiproductIso, biproduct.ι_desc]

@[reassoc]
private theorem pullback_map_ι_comp (f : Y ⟶ X) {I : Type} [Fintype I]
    (M : I → X.Modules) (i : I) :
    (Scheme.Modules.pullback f).map (biproduct.ι M i) ≫
      ((Scheme.Modules.pullback f).mapBiproduct M).hom =
        biproduct.ι (fun j => (Scheme.Modules.pullback f).obj (M j)) i := by
  classical
  apply biproduct.hom_ext
  intro j
  dsimp only [Function.comp_def]
  simp only [Functor.mapBiproduct_hom, Category.assoc, biproduct.lift_π,
    ← Functor.map_comp]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- The dual pullback comparison for a finite sum is assembled from the canonical line comparisons. -/
def splitDualPullbackIso (f : Y ⟶ X) {I : Type} [Fintype I]
    (L : I → Line.Bundles.LineBundle X) :
    (Scheme.Modules.pullback f).obj (dual (⨁ fun i => (L i).sheaf)) ≅
      dual ((Scheme.Modules.pullback f).obj (⨁ fun i => (L i).sheaf)) :=
  (Scheme.Modules.pullback f).mapIso (dualBiproductIso (fun i => (L i).sheaf)) ≪≫
    (Scheme.Modules.pullback f).mapBiproduct (fun i => dual (L i).sheaf) ≪≫
    biproduct.mapIso (fun i => lineDualPullbackIso f (L i)) ≪≫
    (dualBiproductIso (fun i => (Scheme.Modules.pullback f).obj (L i).sheaf)).symm ≪≫
    (dualIso ((Scheme.Modules.pullback f).mapBiproduct (fun i => (L i).sheaf))).symm

/-- On each dual summand the finite-sum comparison is the canonical line comparison. -/
@[reassoc]
theorem splitDualPullbackIso_projection (f : Y ⟶ X) {I : Type} [Fintype I]
    (L : I → Line.Bundles.LineBundle X) (i : I) :
    (Scheme.Modules.pullback f).map (dualMap (biproduct.π (fun j => (L j).sheaf) i)) ≫
        (splitDualPullbackIso f L).hom =
      (lineDualPullbackIso f (L i)).hom ≫
        dualMap ((Scheme.Modules.pullback f).map (biproduct.π (fun j => (L j).sheaf) i)) := by
  let F := Scheme.Modules.pullback f
  let M := fun j => (L j).sheaf
  dsimp only [splitDualPullbackIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Functor.map_comp_assoc, dualMap_projection_comp]
  rw [pullback_map_ι_comp_assoc]
  simp only [biproduct.mapIso_hom, biproduct.ι_map_assoc]
  rw [dualBiproductIso_inv_projection_assoc]
  change (lineDualPullbackIso f (L i)).hom ≫
      dualMap (biproduct.π (F.obj ∘ M) i) ≫ dualMap (F.mapBiproduct M).hom = _
  rw [← dualMap_comp]
  congr 2
  dsimp only [Function.comp_def]
  simp only [Functor.mapBiproduct_hom, biproduct.lift_π]
  rfl

/-- Finite-sum dual base change is natural on every map from a line bundle. -/
theorem splitDualPullbackIso_naturality_from_line (f : Y ⟶ X) {I : Type} [Fintype I]
    (L : I → Line.Bundles.LineBundle X) (R : Line.Bundles.LineBundle X)
    (i : R.sheaf ⟶ ⨁ fun j => (L j).sheaf) :
    (Scheme.Modules.pullback f).map (dualMap i) ≫ (lineDualPullbackIso f R).hom =
      (splitDualPullbackIso f L).hom ≫ dualMap ((Scheme.Modules.pullback f).map i) := by
  let F := Scheme.Modules.pullback f
  let M := fun j => (L j).sheaf
  let a := F.mapIso (dualBiproductIso M) ≪≫ F.mapBiproduct (fun j => dual (M j))
  apply (cancel_epi a.inv).mp
  apply biproduct.hom_ext'
  intro j
  have hj : biproduct.ι (fun j => F.obj (dual (M j))) j ≫ a.inv =
      F.map (dualMap (biproduct.π M j)) := by
    dsimp only [a, Iso.trans_inv, Functor.mapIso_inv]
    rw [Functor.mapBiproduct_inv]
    simp only [biproduct.ι_desc_assoc]
    rw [← F.map_comp, dualBiproductIso_inv_projection]
  change (biproduct.ι (fun j => F.obj (dual (M j))) j ≫ a.inv) ≫
      F.map (dualMap i) ≫ (lineDualPullbackIso f R).hom =
    (biproduct.ι (fun j => F.obj (dual (M j))) j ≫ a.inv) ≫
      (splitDualPullbackIso f L).hom ≫ dualMap (F.map i)
  rw [hj, splitDualPullbackIso_projection_assoc]
  rw [← F.map_comp_assoc, ← dualMap_comp]
  rw [← dualMap_comp, ← F.map_comp]
  exact lineDualPullback_naturality f R (L j) (i ≫ biproduct.π M j)

end SteinerGeometry.SheafDual
