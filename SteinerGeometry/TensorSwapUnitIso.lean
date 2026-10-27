import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers

/-! A shared canonical isomorphism for unit removal followed by tensor symmetry. -/
noncomputable section
namespace SteinerGeometry.TensorSwapUnitIso
open CategoryTheory AlgebraicGeometry MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u
attribute [local instance] TwistPowers.MvPolynomial.instMonoidalCategoryModules_oAI
local instance (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Monoidal.Scheme.Modules.symmetricCategory X

/-- Remove the unit from the left factor and exchange the resulting pair. -/
def iso {X : Scheme.{u}} (M N : X.Modules) :
    (𝟙_ X.Modules ⊗ M) ⊗ N ≅ N ⊗ M :=
  ((λ_ M) ⊗ᵢ Iso.refl N) ≪≫ β_ M N

end SteinerGeometry.TensorSwapUnitIso
