import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.StructureModuleComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalSectionsFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ChartCoefficientSections
import Mathlib.Basic.Complex.Basic

noncomputable section

namespace SteinerGeometry.PointSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

/-- Actual coefficient sections of an affine structure sheaf recover the
original coefficient algebra. -/
def specStructureSectionsEquiv (R : Type) [CommRing R] [Algebra ℂ R] :
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))).obj
        (Line.Bundles.structureModule (Spec (.of R))) ≃ₗ[ℂ] R := by
  let b : Spec (.of R) ⟶ Spec (.of ℂ) := Spec.map (CommRingCat.ofHom (algebraMap ℂ R))
  let e₁ := Coefficient.StructureModuleComparison.coefficientStructureModuleComponent
    (Coefficient.ModulePresheaf.schemeCoefficientMap b) (⊤ : (Spec (.of R)).Opens)
  let e₂ := Affine.ChartCoefficientSections.affineChartCoefficientAlgEquiv b
    (⊤ : (Spec (.of R)).Opens) (Spec (.of R)).topIso.symm (by
      rw [Iso.symm_hom, ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp])
  exact e₁.trans e₂.toLinearEquiv

theorem spec_structure_sections_finrank (R : Type) [CommRing R] [Algebra ℂ R] :
    Module.finrank ℂ ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))).obj
        (Line.Bundles.structureModule (Spec (.of R)))) = Module.finrank ℂ R :=
  (specStructureSectionsEquiv R).finrank_eq

theorem complexPoint_structure_sections_finrank :
    Module.finrank ℂ ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor
      (𝟙 (Spec (.of ℂ)))).obj (Line.Bundles.structureModule (Spec (.of ℂ)))) = 1 := by
  have h := spec_structure_sections_finrank ℂ
  have hb : Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ)) = 𝟙 (Spec (.of ℂ)) := by
    change Spec.map (𝟙 (CommRingCat.of ℂ)) = 𝟙 _
    exact Spec.map_id _
  rw [hb] at h
  simpa using h

end SteinerGeometry.PointSections
