module

public import SteinerGeometry.NativeCohomology

set_option backward.privateInPublic true
@[expose] public section

namespace SteinerGeometry.EllipticCohomology
open AlgebraicGeometry CategoryTheory
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

instance nativeCoefficientCohomologyFunctor_additive {X : Scheme.{0}}
    (p : X ⟶ Spec (.of ℂ)) (q : ℕ) :
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).Additive := by
  unfold Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
  infer_instance

end SteinerGeometry.EllipticCohomology
