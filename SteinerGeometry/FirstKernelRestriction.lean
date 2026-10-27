import SteinerGeometry.SymmetricKernelChart
import SteinerGeometry.ContractionRestriction
import SteinerGeometry.ContractionTargetIso

/-! Restriction of the first evaluation-kernel data and its canonical columns. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
local instance firstKernelRestrictionBiproducts (Z : Scheme.{u}) : HasFiniteBiproducts Z.Modules := HasFiniteBiproducts.of_hasFiniteProducts
private instance firstKernelRestrictionRestrictionAdditive : (Scheme.Modules.restrictFunctor f).Additive where
  map_add := by intros; ext U x; rfl
private instance firstKernelRestrictionRestrictionFiniteLimits : PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) := by
  let _ : PreservesLimits (Scheme.Modules.restrictFunctor f) :=
    Module.RestrictionLimits.moduleRestrictFunctor_preservesLimits f
  infer_instance

/-- Restriction of the original finite free module, before symmetric labels are introduced. -/
def freeLinearRestrictIso (n : ℕ) :
    (⨁ fun _ : Fin (n+1) => Line.Bundles.structureModule Y).restrict f ≅
      (⨁ fun _ : Fin (n+1) => Line.Bundles.structureModule X) :=
  restrictBiproductIso f (fun _ : Fin (n+1) => Line.Bundles.structureModule Y) ≪≫
    biproduct.mapIso (fun _ => Scheme.Modules.restrictUnitIso f)

@[simp, reassoc] theorem freeLinearRestrictIso_hom_π (n : ℕ) (i : Fin (n+1)) :
    (freeLinearRestrictIso f n).hom ≫ biproduct.π _ i =
      (Scheme.Modules.restrictFunctor f).map (biproduct.π _ i) ≫
        (Scheme.Modules.restrictUnitIso f).hom := by
  simp only [freeLinearRestrictIso, Iso.trans_hom, Category.assoc, biproduct.mapIso_hom,
    biproduct.map_π, restrictBiproductIso, biproduct.lift_π_assoc]

@[simp] theorem freeLinearRestrictIso_ι_inv (n : ℕ) (i : Fin (n+1)) :
    biproduct.ι (fun _ : Fin (n+1) => Line.Bundles.structureModule X) i ≫
      (freeLinearRestrictIso f n).inv =
        (Scheme.Modules.restrictUnitIso f).inv ≫
          (Scheme.Modules.restrictFunctor f).map
            (biproduct.ι (fun _ : Fin (n+1) => Line.Bundles.structureModule Y) i) := by
  change _ ≫ (biproduct.map (fun _ => (Scheme.Modules.restrictUnitIso f).inv) ≫
    biproduct.desc (fun i => (Scheme.Modules.restrictFunctor f).map
      (biproduct.ι (fun _ : Fin (n+1) => Line.Bundles.structureModule Y) i))) = _
  rw [← Category.assoc, biproduct.ι_map, Category.assoc, biproduct.ι_desc]

/-- Restriction commutes with the original evaluation map. -/
theorem structureEvaluation_restrict {n : ℕ} {N : Y.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule Y ⟶ N)) :
    (freeLinearRestrictIso f n).inv ≫
      (Scheme.Modules.restrictFunctor f).map (structureEvaluation e) =
        structureEvaluation (restrictedEvaluation f e) := by
  apply biproduct.hom_ext'
  intro i
  rw [← Category.assoc, freeLinearRestrictIso_ι_inv, Category.assoc,
    ← Functor.map_comp, show biproduct.ι _ i ≫ structureEvaluation e = e i from biproduct.ι_desc e i]
  exact (biproduct.ι_desc (restrictedEvaluation f e) i).symm

/-- The actual first kernel commutes with restriction. -/
def firstKernelRestrictIso {n : ℕ} {N : Y.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule Y ⟶ N)) :
    (kernel (structureEvaluation e)).restrict f ≅
      kernel (structureEvaluation (restrictedEvaluation f e)) :=
  PreservesKernel.iso (Scheme.Modules.restrictFunctor f) (structureEvaluation e) ≪≫
    kernel.mapIso _ _ (freeLinearRestrictIso f n) (Iso.refl _) (by
      apply (cancel_epi (freeLinearRestrictIso f n).inv).mp
      simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id] using
        structureEvaluation_restrict f e)

@[simp, reassoc] theorem firstKernelRestrictIso_hom_ι {n : ℕ} {N : Y.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule Y ⟶ N)) :
    (firstKernelRestrictIso f e).hom ≫ kernel.ι (structureEvaluation (restrictedEvaluation f e)) =
      (Scheme.Modules.restrictFunctor f).map (kernel.ι (structureEvaluation e)) ≫
        (freeLinearRestrictIso f n).hom := by
  simp [firstKernelRestrictIso, PreservesKernel.iso_hom]

/-- Restricting a genuine direct-sum splitting gives a genuine splitting of the local kernel. -/
def firstKernelSplittingRestrict {n : ℕ} {N : Y.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule Y ⟶ N))
    (L : Fin n → Line.Bundles.LineBundle Y)
    (E : (⨁ fun j => (L j).sheaf) ≅ kernel (structureEvaluation e)) :
    (⨁ fun j => (restrictionLineBundle f (L j)).sheaf) ≅
      kernel (structureEvaluation (restrictedEvaluation f e)) :=
  (restrictBiproductIso f (fun j => (L j).sheaf)).symm ≪≫
    (Scheme.Modules.restrictFunctor f).mapIso E ≪≫ firstKernelRestrictIso f e

/-- The degree-one reindexing is natural under restriction. -/
theorem linearMonomialIso_restrict (n : ℕ) :
    (Scheme.Modules.restrictFunctor f).map (linearMonomialIso (X := Y) n).hom ≫
      (freeMonomialRestrictIso f n 1).hom =
        (freeLinearRestrictIso f n).hom ≫ (linearMonomialIso (X := X) n).hom := by
  apply biproduct.hom_ext
  intro b
  obtain ⟨i, rfl⟩ := (Sym.oneEquiv : Fin (n+1) ≃ Sym (Fin (n+1)) 1).surjective b
  have hi : (Sym.oneEquiv : Fin (n+1) ≃ Sym (Fin (n+1)) 1) i =
      wordMonomial (fun _ : Fin 1 => i) := by apply Sym.ext; rfl
  rw [hi]
  simp only [Category.assoc, freeMonomialRestrictIso_hom_π, linearMonomialIso_hom_π,
    freeLinearRestrictIso_hom_π, ← Functor.map_comp_assoc]

/-- The canonical columns obtained from the first kernel splitting commute with restriction. -/
theorem firstKernelColumns_restrict {n : ℕ} {N : Y.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule Y ⟶ N))
    (L : Fin n → Line.Bundles.LineBundle Y)
    (E : (⨁ fun j => (L j).sheaf) ≅ kernel (structureEvaluation e)) (i : Fin n) :
    restrictedKernelColumns f L (firstKernelColumns e L E) i =
      firstKernelColumns (restrictedEvaluation f e) (fun j => restrictionLineBundle f (L j))
        (firstKernelSplittingRestrict f e L E) i := by
  unfold restrictedKernelColumns firstKernelColumns firstKernelSplittingRestrict
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    firstKernelRestrictIso_hom_ι_assoc, restrictBiproductIso, biproduct.ι_desc_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [linearMonomialIso_restrict]

end SteinerGeometry
