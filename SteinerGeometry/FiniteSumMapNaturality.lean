import SteinerGeometry.ProjectiveKernelBundle
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoproductMatrixComponents

/-! Componentwise naturality of the canonical finite-sum comparison. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.ProjectiveKernelBundle
open CategoryTheory CategoryTheory.Limits
open OAI.AlgebraicGeometry.SheafCohomology.Projective.CoproductMatrixComponents
universe u₁ u₂ v₁ v₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  (F : C ⥤ D) [F.Additive]

@[reassoc (attr := simp)]
theorem finiteSumMapIso_ι (r : ℕ) (M : Fin r → C) (i : Fin r) :
    F.map (Sigma.ι M i) ≫ (finiteSumMapIso F r M).hom =
      Sigma.ι (F.obj ∘ M) i := by
  let : PreservesFiniteBiproducts F := Functor.preservesFiniteBiproductsOfAdditive F
  apply (cancel_mono (finiteSumMapIso F r M).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [finiteSumMapIso, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv,
    Category.assoc, biproduct.isoCoproduct_inv, Sigma.ι_comp_desc_assoc,
    Functor.mapBiproduct_inv, biproduct.ι_desc_assoc, ← F.map_comp,
    biproduct.isoCoproduct_hom, biproduct.ι_desc]

@[reassoc (attr := simp)]
theorem finiteSumMapIso_π (r : ℕ) (M : Fin r → C) (i : Fin r) :
    (finiteSumMapIso F r M).hom ≫ finiteCoproductProjection (F.obj ∘ M) i =
      F.map (finiteCoproductProjection M i) := by
  let : PreservesFiniteBiproducts F := Functor.preservesFiniteBiproductsOfAdditive F
  simp only [finiteSumMapIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    finiteCoproductProjection, Category.assoc, Iso.hom_inv_id_assoc,
    Functor.mapBiproduct_hom, Function.comp_def, biproduct.lift_π, ← F.map_comp]

/-- The canonical finite-sum comparison sends a whole matrix to the matrix
of the functor images of its component maps. -/
theorem finiteSumMapIso_component (r s : ℕ) (M : Fin r → C) (N : Fin s → C)
    (f : (∐ M) ⟶ ∐ N) (i : Fin r) (j : Fin s) :
    Sigma.ι (F.obj ∘ M) i ≫
      (finiteSumMapIso F r M).inv ≫ F.map f ≫ (finiteSumMapIso F s N).hom ≫
        finiteCoproductProjection (F.obj ∘ N) j =
    F.map (Sigma.ι M i ≫ f ≫ finiteCoproductProjection N j) := by
  rw [← finiteSumMapIso_ι F r M i]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, finiteSumMapIso_π]
  simp only [Functor.map_comp]

/-- Further component isomorphisms conjugate each matrix entry individually. -/
theorem finiteSumMapIso_conjugated_component (r s : ℕ) (M : Fin r → C) (N : Fin s → C)
    (M' : Fin r → D) (N' : Fin s → D)
    (eM : ∀ i, F.obj (M i) ≅ M' i) (eN : ∀ j, F.obj (N j) ≅ N' j)
    (f : (∐ M) ⟶ ∐ N) (i : Fin r) (j : Fin s) :
    Sigma.ι M' i ≫
      (finiteSumMapIso F r M ≪≫ Sigma.mapIso eM).inv ≫ F.map f ≫
      (finiteSumMapIso F s N ≪≫ Sigma.mapIso eN).hom ≫ finiteCoproductProjection N' j =
    (eM i).inv ≫ F.map (Sigma.ι M i ≫ f ≫ finiteCoproductProjection N j) ≫ (eN j).hom := by
  have hm : Sigma.ι M' i ≫ (Sigma.mapIso eM).inv =
      (eM i).inv ≫ Sigma.ι (F.obj ∘ M) i := by
    simpa only [Function.comp_def] using (Sigma.ι_mapIso_inv eM i)
  have hn : (Sigma.mapIso eN).hom ≫ finiteCoproductProjection N' j =
      finiteCoproductProjection (F.obj ∘ N) j ≫ (eN j).hom := by
    apply Sigma.hom_ext
    intro k
    by_cases hk : k = j
    · subst k
      simp [finiteCoproductProjection, biproduct.isoCoproduct_inv,
        Function.comp_def, Category.assoc]
    · simp only [finiteCoproductProjection, biproduct.isoCoproduct_inv,
        Category.assoc, Sigma.ι_mapIso_hom_assoc, Sigma.ι_comp_desc_assoc,
        Function.comp_def]
      rw [biproduct.ι_π_ne_assoc _ hk]
      simp [biproduct.ι_π_ne _ hk]
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc]
  rw [← Category.assoc, hm]
  simp only [Category.assoc]
  rw [hn]
  simpa only [Category.assoc] using congrArg (fun z => (eM i).inv ≫ z ≫ (eN j).hom)
    (finiteSumMapIso_component F r s M N f i j)

end SteinerGeometry.ProjectiveKernelBundle
