module

public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheaf
public import Mathlib.Basic.Complex.Basic

set_option backward.privateInPublic true
@[expose] public section

noncomputable section
namespace SteinerGeometry.EllipticCohomology
open CategoryTheory AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

abbrev H {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) (M : X.Modules) (q : ℕ) :=
  (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
    (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj M


end SteinerGeometry.EllipticCohomology
