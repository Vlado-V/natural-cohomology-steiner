import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoproductMatrixComponents

/-! Finite matrix coordinates for the actual additive cohomology functor. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.CohomologyMatrix
open CategoryTheory CategoryTheory.Limits
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u v w z
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable {R : Type w} [Ring R]
variable (F : C ⥤ ModuleCat.{z} R) [F.Additive]
variable {ι κ : Type} [Fintype ι] [Fintype κ]

def sumEquiv (M : ι → C) : F.obj (∐ M) ≃ₗ[R] (i : ι) → F.obj (M i) := by
  letI : HasFiniteBiproducts (ModuleCat.{z} R) := HasFiniteBiproducts.of_hasFiniteProducts
  letI : PreservesFiniteBiproducts F := Functor.preservesFiniteBiproductsOfAdditive F
  exact (F.mapIso (biproduct.isoCoproduct M).symm ≪≫ F.mapBiproduct M ≪≫
    biproduct.isoProduct (F.obj ∘ M) ≪≫ ModuleCat.piIsoPi (F.obj ∘ M)).toLinearEquiv

theorem sumEquiv_apply (M : ι → C) (x : F.obj (∐ M)) (i : ι) :
    sumEquiv F M x i = (F.map (CoproductMatrixComponents.finiteCoproductProjection M i)) x := by
  letI : HasFiniteBiproducts (ModuleCat.{z} R) := HasFiniteBiproducts.of_hasFiniteProducts
  letI : PreservesFiniteBiproducts F := Functor.preservesFiniteBiproductsOfAdditive F
  have h : F.map (biproduct.isoCoproduct M).inv ≫ (F.mapBiproduct M).hom ≫
      (biproduct.isoProduct (F.obj ∘ M)).hom ≫ (ModuleCat.piIsoPi (F.obj ∘ M)).hom ≫
        ModuleCat.ofHom (LinearMap.proj i) =
      F.map (CoproductMatrixComponents.finiteCoproductProjection M i) := by
    simp only [ModuleCat.piIsoPi_hom_ker_subtype, biproduct.isoProduct_hom,
      Category.assoc, Pi.lift_comp_π, Functor.mapBiproduct_hom, biproduct.lift_π]
    erw [biproduct.lift_π]
    rw [← F.map_comp]
    rfl
  exact ConcreteCategory.congr_hom h x

theorem identity_sum (M : ι → C) :
    ∑ i, CoproductMatrixComponents.finiteCoproductProjection M i ≫ Sigma.ι M i =
      𝟙 (∐ M) := by
  apply (cancel_epi (biproduct.isoCoproduct M).hom).1
  rw [Preadditive.comp_sum]
  simp only [CoproductMatrixComponents.finiteCoproductProjection, Iso.hom_inv_id_assoc]
  have hi (i : ι) : Sigma.ι M i = biproduct.ι M i ≫ (biproduct.isoCoproduct M).hom := by
    simp
  simp only [hi, ← Category.assoc]
  simp only [Iso.hom_inv_id, Category.id_comp]
  rw [← Preadditive.sum_comp, biproduct.total]
  simp

/-- In finite-sum coordinates, an actual map acts by the matrix of its
actual component maps. -/
theorem sumEquiv_map (M : ι → C) (N : κ → C) (f : (∐ M) ⟶ ∐ N)
    (x : F.obj (∐ M)) (j : κ) :
    sumEquiv F N ((F.map f) x) j =
      ∑ i, (F.map (Sigma.ι M i ≫ f ≫
        CoproductMatrixComponents.finiteCoproductProjection N j)) (sumEquiv F M x i) := by
  simp only [sumEquiv_apply]
  have h : f ≫ CoproductMatrixComponents.finiteCoproductProjection N j =
      ∑ i, CoproductMatrixComponents.finiteCoproductProjection M i ≫
        (Sigma.ι M i ≫ f ≫ CoproductMatrixComponents.finiteCoproductProjection N j) := by
    calc
      _ = (𝟙 (∐ M)) ≫ f ≫ CoproductMatrixComponents.finiteCoproductProjection N j := by simp
      _ = (∑ i, CoproductMatrixComponents.finiteCoproductProjection M i ≫ Sigma.ι M i) ≫
          f ≫ CoproductMatrixComponents.finiteCoproductProjection N j := by rw [identity_sum]
      _ = _ := by simp only [Preadditive.sum_comp, Category.assoc]
  have hh := congrArg (fun q : F.obj (∐ M) ⟶ F.obj (N j) => q x)
    (congrArg F.map h)
  simpa only [F.map_sum, F.map_comp, ModuleCat.hom_sum, LinearMap.sum_apply,
    ModuleCat.comp_apply] using hh

section Coordinates
variable (M : ι → C) (N : κ → C)
variable {A : ι → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
variable {B : κ → Type*} [∀ j, AddCommGroup (B j)] [∀ j, Module R (B j)]

def sumCoordinates (e : ∀ i, F.obj (M i) ≃ₗ[R] A i) :
    F.obj (∐ M) ≃ₗ[R] ((i : ι) → A i) :=
  (sumEquiv F M).trans (LinearEquiv.piCongrRight e)

def matrixLinearMap (g : ∀ j i, A i →ₗ[R] B j) :
    ((i : ι) → A i) →ₗ[R] ((j : κ) → B j) :=
  LinearMap.pi fun j => ∑ i, (g j i).comp (LinearMap.proj i)

/-- Entrywise naturality assembles into naturality of the full actual
cohomology matrix. -/
theorem sumCoordinates_map (f : (∐ M) ⟶ ∐ N)
    (eA : ∀ i, F.obj (M i) ≃ₗ[R] A i)
    (eB : ∀ j, F.obj (N j) ≃ₗ[R] B j)
    (g : ∀ j i, A i →ₗ[R] B j)
    (h : ∀ i j x, eB j ((F.map (Sigma.ι M i ≫ f ≫
      CoproductMatrixComponents.finiteCoproductProjection N j)) x) = g j i (eA i x))
    (x : F.obj (∐ M)) :
    sumCoordinates F N eB ((F.map f) x) =
      matrixLinearMap g (sumCoordinates F M eA x) := by
  funext j
  change eB j (sumEquiv F N ((F.map f) x) j) = _
  rw [sumEquiv_map, map_sum]
  simp only [matrixLinearMap, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]
  change (∑ i, eB j ((F.map (Sigma.ι M i ≫ f ≫
      CoproductMatrixComponents.finiteCoproductProjection N j)) (sumEquiv F M x i))) =
    ∑ i, g j i (eA i (sumEquiv F M x i))
  exact Finset.sum_congr rfl (fun i _ => h i j _)
end Coordinates

end SteinerGeometry.CohomologyMatrix
