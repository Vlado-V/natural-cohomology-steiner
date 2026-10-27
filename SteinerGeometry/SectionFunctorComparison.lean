module

public import SteinerGeometry.CurveSectionFunctor
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalSectionsFunctor

set_option backward.privateInPublic true
@[expose] public section

noncomputable section
namespace SteinerGeometry
open CategoryTheory AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

/-- The coefficient-section convention used by the finite isogeny calculation
and the native section functor used in the curve argument agree canonically. -/
def sectionFunctorCoefficientEquiv {K : Type} [CommRing K]
    {X : Scheme} (p : X ⟶ Spec (.of K)) (M : X.Modules) :
    (sectionFunctor p).obj M ≃ₗ[K]
      (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M where
  toFun s := s
  invFun s := s
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r s := by
    change (M.smul _).hom s = (M.smul _).hom s
    congr 2
    simp [Coefficient.ModulePresheaf.schemeCoefficientMap]

end SteinerGeometry
