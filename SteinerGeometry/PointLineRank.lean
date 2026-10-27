module

public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointLineBundleTriviality
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalSectionsFunctor
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.StructureModuleComparison
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Category.ModuleCat.Products

set_option backward.privateInPublic true
@[expose] public section

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

namespace SteinerGeometry

/-- An actual line bundle on a field point has a one-dimensional space of sections. -/
theorem fieldLine_sections_finrank_one {K : Type} [Field K] (L : Line.Bundles.LineBundle (Spec (.of K))) :
    Module.finrank K
      ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (𝟙 (Spec (.of K)))).obj
        L.sheaf) = 1 := by
  let c := Coefficient.ModulePresheaf.schemeCoefficientMap (𝟙 (Spec (.of K)))
  let eM := ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor
    (𝟙 (Spec (.of K)))).mapIso L.trivialization_of_subsingleton).toLinearEquiv
  let eO :
      (Coefficient.ModulePresheaf.coefficientModulePresheaf c
        (Line.Bundles.structureModule (Spec (.of K)))).obj (.op ⊤) ≃ₗ[K]
      Coefficient.AlgebraPresheaf.coefficientAlgebraSections c ⊤ :=
    Coefficient.StructureModuleComparison.coefficientStructureModuleComponent c ⊤
  apply (eM.trans eO).finrank_eq.trans
  apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
  change Function.Bijective (Coefficient.AlgebraPresheaf.coefficientSectionMap c ⊤)
  dsimp [Coefficient.AlgebraPresheaf.coefficientSectionMap, c,
    Coefficient.ModulePresheaf.schemeCoefficientMap]
  change Function.Bijective (fun k => (Spec (.of K)).presheaf.map
    (𝟙 (.op (⊤ : (Spec (.of K)).Opens))) ((Scheme.ΓSpecIso (.of K)).inv k))
  rw [(Spec (.of K)).presheaf.map_id]
  exact ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv

/-- A finite sum of point line bundles has one dimension per summand. -/
theorem fieldLine_coproduct_sections_finrank {K : Type} [Field K]
    {I : Type} [Fintype I] (L : I → Line.Bundles.LineBundle (Spec (.of K))) :
    Module.finrank K
      ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (𝟙 (Spec (.of K)))).obj
        (∐ fun i => (L i).sheaf)) = Fintype.card I := by
  let F := Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (𝟙 (Spec (.of K)))
  let M := fun i => (L i).sheaf
  have : F.Additive := by
    constructor
    change ∀ {M N : (Spec (.of K)).Modules} {f g : M ⟶ N},
      F.map (f + g) = F.map f + F.map g
    intro M N f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl
  have hM (i : I) : Module.Finite K (F.obj (M i)) :=
    Module.finite_of_finrank_eq_succ (fieldLine_sections_finrank_one (L i))
  let : HasBiproduct (F.obj ∘ M) := HasBiproduct.of_hasProduct (F.obj ∘ M)
  let e : F.obj (∐ M) ≅ ModuleCat.of K (∀ i, F.obj (M i)) :=
    PreservesCoproduct.iso F M ≪≫ (biproduct.isoCoproduct (F.obj ∘ M)).symm ≪≫
      biproduct.isoProduct (F.obj ∘ M) ≪≫ ModuleCat.piIsoPi (F.obj ∘ M)
  have : ∀ i, Module.Finite K (F.obj (M i)) := hM
  exact e.toLinearEquiv.finrank_eq.trans
    ((Module.finrank_pi_fintype K).trans
      (by simp [M, F, fieldLine_sections_finrank_one]))

end SteinerGeometry
