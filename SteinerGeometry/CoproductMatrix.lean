module

public import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoproductMatrixComponents

set_option backward.privateInPublic true
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
open OAI.AlgebraicGeometry.SheafCohomology.Projective
namespace SteinerGeometry
universe u v
section CoproductMatrix
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- A matrix of actual component morphisms assembled into a morphism of finite sums. -/
def finiteCoproductFromMatrix (M : ι → C) (N : κ → C)
    (c : ∀ j i, M i ⟶ N j) : (∐ M) ⟶ ∐ N :=
  Sigma.desc fun i => biproduct.lift (fun j => c j i) ≫ (biproduct.isoCoproduct N).hom

@[reassoc (attr := simp)]
theorem finiteCoproductFromMatrix_component (M : ι → C) (N : κ → C)
    (c : ∀ j i, M i ⟶ N j) (i : ι) (j : κ) :
    Sigma.ι M i ≫ finiteCoproductFromMatrix M N c ≫
      CoproductMatrixComponents.finiteCoproductProjection N j = c j i := by
  unfold finiteCoproductFromMatrix CoproductMatrixComponents.finiteCoproductProjection
  rw [Sigma.ι_comp_desc_assoc, Category.assoc, Iso.hom_inv_id_assoc, biproduct.lift_π]

/-- The polynomial encodings of individual component maps assemble faithfully and surjectively. -/
def finiteCoproductEncodedMatrixEquiv (M : ι → C) (N : κ → C)
    {P : κ → ι → Type*} (e : ∀ j i, (M i ⟶ N j) ≃ P j i) :
    ((∐ M) ⟶ ∐ N) ≃ (∀ j i, P j i) where
  toFun := CoproductMatrixComponents.finiteCoproductEncodedMatrix M N e
  invFun := fun p => finiteCoproductFromMatrix M N fun j i => (e j i).symm (p j i)
  left_inv f := by
    apply CoproductMatrixComponents.finiteCoproduct_matrix_ext M N
    intro i j
    simp [CoproductMatrixComponents.finiteCoproductEncodedMatrix]
  right_inv p := by
    funext j i
    simp [CoproductMatrixComponents.finiteCoproductEncodedMatrix]

theorem finiteCoproductEncodedMatrixEquiv_symm_apply (M : ι → C) (N : κ → C)
    {P : κ → ι → Type*} (e : ∀ j i, (M i ⟶ N j) ≃ P j i)
    (p : ∀ j i, P j i) :
    (finiteCoproductEncodedMatrixEquiv M N e).symm p =
      finiteCoproductFromMatrix M N (fun j i => (e j i).symm (p j i)) := rfl

@[reassoc (attr := simp)]
theorem finiteCoproduct_mapIso_projection (M N : κ → C)
    (e : ∀ j, M j ≅ N j) (j : κ) :
    (Sigma.mapIso e).hom ≫ CoproductMatrixComponents.finiteCoproductProjection N j =
      CoproductMatrixComponents.finiteCoproductProjection M j ≫ (e j).hom := by
  apply Sigma.hom_ext
  intro k
  unfold CoproductMatrixComponents.finiteCoproductProjection
  simp only [Category.assoc, Sigma.ι_mapIso_hom_assoc, biproduct.isoCoproduct_inv,
    Sigma.ι_comp_desc_assoc]
  by_cases h : k = j
  · subst j
    simp
  · simp [h]

theorem finiteCoproductFromMatrix_postcompose (M : ι → C) (N P : κ → C)
    (c : ∀ j i, M i ⟶ N j) (e : ∀ j, N j ≅ P j) :
    finiteCoproductFromMatrix M N c ≫ (Sigma.mapIso e).hom =
      finiteCoproductFromMatrix M P (fun j i => c j i ≫ (e j).hom) := by
  apply CoproductMatrixComponents.finiteCoproduct_matrix_ext
  intro i j
  simp only [Category.assoc, finiteCoproduct_mapIso_projection,
    finiteCoproductFromMatrix_component_assoc, finiteCoproductFromMatrix_component]
end CoproductMatrix

end SteinerGeometry
