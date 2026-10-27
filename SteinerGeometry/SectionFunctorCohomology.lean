module

public import SteinerGeometry.CohomologySections
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.DegreeZero

set_option backward.privateInPublic true
@[expose] public section

noncomputable section
namespace SteinerGeometry
open CategoryTheory AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

/-- The coefficient convention in the curve construction is the native global
section convention, transported by its canonical identity map. -/
def sectionFunctorNativeEquiv {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) (M : X.Modules) :
    (sectionFunctor p).obj M ≃ₗ[ℂ]
      (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M :=
  (Global.ModuleSectionIdentity.coefficientGlobalSectionsNativeIso
    (Coefficient.ModulePresheaf.schemeCoefficientMap p) M).symm

def cohomologyZeroSectionFunctorEquiv {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ))
    (M : X.Modules) : EllipticCohomology.H p M 0 ≃ₗ[ℂ] (sectionFunctor p).obj M :=
  (CoefficientCohomology.DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv
    (Coefficient.ModulePresheaf.schemeCoefficientMap p) M).trans
      (sectionFunctorNativeEquiv p M).symm

theorem sectionFunctor_finrank_eq_native {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ))
    (M : X.Modules) :
    Module.finrank ℂ ((sectionFunctor p).obj M) =
      Module.finrank ℂ ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M) :=
  (sectionFunctorNativeEquiv p M).finrank_eq

end SteinerGeometry
