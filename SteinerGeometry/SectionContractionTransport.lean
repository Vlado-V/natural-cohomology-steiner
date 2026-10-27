import SteinerGeometry.SectionContractionCategory

/-! Isomorphism transport for the literal symmetric contraction matrix. -/
noncomputable section
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable {A B D E : C} {n : ℕ}

/-- Changing the target of the coefficient maps changes the contraction target componentwise. -/
theorem sectionContraction_postcompose (T : Fin (n+1) → (B ⟶ D)) (g : D ⟶ E) (d : ℕ) :
    sectionContraction T d ≫ biproduct.map (fun _ : Sym (Fin (n+1)) d => g) =
      sectionContraction (fun i => T i ≫ g) d := by
  classical
  apply biproduct.hom_ext'
  intro a
  apply biproduct.hom_ext
  intro b
  simp only [Category.assoc, biproduct.map_π]
  rw [sectionContraction_component]
  simpa only [Category.assoc, Preadditive.sum_comp, Preadditive.nsmul_comp] using
    congrArg (fun q => q ≫ g) (sectionContraction_component T d a b)

/-- Changing the source of the coefficient maps changes the contraction source componentwise. -/
theorem sectionContraction_precompose (h : A ⟶ B) (T : Fin (n+1) → (B ⟶ D)) (d : ℕ) :
    biproduct.map (fun _ : Sym (Fin (n+1)) (d+1) => h) ≫ sectionContraction T d =
      sectionContraction (fun i => h ≫ T i) d := by
  classical
  apply biproduct.hom_ext'
  intro a
  apply biproduct.hom_ext
  intro b
  rw [← Category.assoc, biproduct.ι_map]
  simp only [Category.assoc]
  rw [sectionContraction_component, sectionContraction_component]
  simp only [Preadditive.comp_sum, Preadditive.comp_nsmul]

end SteinerGeometry
