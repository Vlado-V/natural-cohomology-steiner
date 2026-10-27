import SteinerGeometry.SymmetricRestriction
import SteinerGeometry.SectionContractionTransport
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.RestrictionLimits

/-! Restriction of the actual contraction kernel and its canonical monomial map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
local instance contractionRestrictionBiproducts (Z : Scheme.{u}) : HasFiniteBiproducts Z.Modules := HasFiniteBiproducts.of_hasFiniteProducts
private instance contractionRestrictionRestrictionAdditive : (Scheme.Modules.restrictFunctor f).Additive where
  map_add := by intros; ext U x; rfl
private instance contractionRestrictionRestrictionFiniteLimits : PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) := by
  let _ : PreservesLimits (Scheme.Modules.restrictFunctor f) :=
    Module.RestrictionLimits.moduleRestrictFunctor_preservesLimits f
  infer_instance

@[simp] theorem freeMonomialRestrictIso_ι_inv (n d : ℕ) (a : Sym (Fin (n+1)) d) :
    biproduct.ι (fun _ : Sym (Fin (n+1)) d => Line.Bundles.structureModule X) a ≫
      (freeMonomialRestrictIso f n d).inv =
        (Scheme.Modules.restrictUnitIso f).inv ≫
          (Scheme.Modules.restrictFunctor f).map
            (biproduct.ι (fun _ : Sym (Fin (n+1)) d => Line.Bundles.structureModule Y) a) := by
  change _ ≫ (biproduct.map (fun _ => (Scheme.Modules.restrictUnitIso f).inv) ≫
    biproduct.desc (fun a => (Scheme.Modules.restrictFunctor f).map
      (biproduct.ι (fun _ : Sym (Fin (n+1)) d => Line.Bundles.structureModule Y) a))) = _
  rw [← Category.assoc, biproduct.ι_map, Category.assoc, biproduct.ι_desc]

/-- Actual restricted sections, normalized by the canonical frame of the structure sheaf. -/
def restrictedEvaluation {n : ℕ} {N : Y.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule Y ⟶ N)) :
    Fin (n+1) → (Line.Bundles.structureModule X ⟶ N.restrict f) :=
  fun i => (Scheme.Modules.restrictUnitIso f).inv ≫ (Scheme.Modules.restrictFunctor f).map (e i)

/-- Contraction commutes with restriction, including both finite-sum identifications. -/
theorem sectionContraction_restrict {n d : ℕ} {N : Y.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule Y ⟶ N)) :
    (freeMonomialRestrictIso f n (d+1)).inv ≫
      (Scheme.Modules.restrictFunctor f).map (sectionContraction e d) ≫
      (restrictBiproductIso f (fun _ : Sym (Fin (n+1)) d => N)).hom =
        sectionContraction (restrictedEvaluation f e) d := by
  classical
  apply biproduct.hom_ext'
  intro a
  apply biproduct.hom_ext
  intro b
  rw [← Category.assoc, ← Category.assoc, freeMonomialRestrictIso_ι_inv]
  simp only [Category.assoc, restrictBiproductIso, biproduct.lift_π]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp]
  simp only [Category.assoc]
  rw [sectionContraction_component, sectionContraction_component]
  simp only [Functor.map_sum, Functor.map_nsmul, Preadditive.comp_sum, Preadditive.comp_nsmul,
    restrictedEvaluation]

/-- The restricted genuine kernel is the kernel of the restricted coefficient contraction. -/
def contractionRestrictKernelIso {n d : ℕ} {N : Y.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule Y ⟶ N)) :
    (kernel (sectionContraction e d)).restrict f ≅
      kernel (sectionContraction (restrictedEvaluation f e) d) :=
  PreservesKernel.iso (Scheme.Modules.restrictFunctor f) (sectionContraction e d) ≪≫
    kernel.mapIso _ _ (freeMonomialRestrictIso f n (d+1))
      (restrictBiproductIso f (fun _ : Sym (Fin (n+1)) d => N)) (by
        apply (cancel_epi (freeMonomialRestrictIso f n (d+1)).inv).mp
        simpa only [Category.assoc, Iso.inv_hom_id_assoc] using sectionContraction_restrict f e)

@[simp, reassoc] theorem contractionRestrictKernelIso_hom_ι {n d : ℕ} {N : Y.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule Y ⟶ N)) :
    (contractionRestrictKernelIso (d := d) f e).hom ≫
      kernel.ι (sectionContraction (restrictedEvaluation f e) d) =
        (Scheme.Modules.restrictFunctor f).map (kernel.ι (sectionContraction e d)) ≫
          (freeMonomialRestrictIso f n (d+1)).hom := by
  simp [contractionRestrictKernelIso, PreservesKernel.iso_hom]

/-- Restrict the actual linear-form columns into the canonical local free monomial frame. -/
def restrictedKernelColumns {m n : ℕ} (L : Fin m → Line.Bundles.LineBundle Y)
    (c : ∀ j, (L j).sheaf ⟶ homogeneousFreeSheaf (X := Y) n 1) :
    ∀ j, (restrictionLineBundle f (L j)).sheaf ⟶ homogeneousFreeSheaf (X := X) n 1 :=
  fun j => (Scheme.Modules.restrictFunctor f).map (c j) ≫ (freeMonomialRestrictIso f n 1).hom

/-- The evaluation-kernel relation is preserved by literal restriction. -/
theorem restrictedKernelColumns_relation {m n : ℕ} {N : Y.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule Y ⟶ N))
    (L : Fin m → Line.Bundles.LineBundle Y)
    (c : ∀ j, (L j).sheaf ⟶ homogeneousFreeSheaf (X := Y) n 1)
    (hc : ∀ j, ∑ i, (c j ≫ biproduct.π _ (wordMonomial (fun _ : Fin 1 => i))) ≫ e i = 0) :
    ∀ j, ∑ i, (restrictedKernelColumns f L c j ≫
      biproduct.π _ (wordMonomial (fun _ : Fin 1 => i))) ≫ restrictedEvaluation f e i = 0 := by
  intro j
  have h := congrArg (Scheme.Modules.restrictFunctor f).map (hc j)
  simpa only [restrictedKernelColumns, restrictedEvaluation, Category.assoc,
    freeMonomialRestrictIso_hom_π, Iso.hom_inv_id_assoc,
    Functor.map_sum, Functor.map_zero, ← Functor.map_comp_assoc, ← Functor.map_comp] using h

/-- The actual canonical map into the contraction kernel commutes with restriction. -/
theorem splitMonomialKernelMap_restrict {m n d : ℕ} {N : Y.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule Y ⟶ N))
    (L : Fin m → Line.Bundles.LineBundle Y)
    (c : ∀ j, (L j).sheaf ⟶ homogeneousFreeSheaf (X := Y) n 1)
    (hc : ∀ j, ∑ i, (c j ≫ biproduct.π _ (wordMonomial (fun _ : Fin 1 => i))) ≫ e i = 0) :
    (splitMonomialSourceRestrictIso f L (d+1)).inv ≫
      (Scheme.Modules.restrictFunctor f).map (splitMonomialKernelMap (d := d) e L c hc) ≫
      (contractionRestrictKernelIso f e).hom =
        splitMonomialKernelMap (d := d) (restrictedEvaluation f e)
          (fun j => restrictionLineBundle f (L j)) (restrictedKernelColumns f L c)
          (restrictedKernelColumns_relation f e L c hc) := by
  apply (cancel_mono (kernel.ι (sectionContraction (restrictedEvaluation f e) d))).mp
  simp only [Category.assoc, contractionRestrictKernelIso_hom_ι,
    ← Functor.map_comp_assoc, splitMonomialKernelMap_ι]
  exact splitMonomialMap_restrict f L c (d+1)

end SteinerGeometry
