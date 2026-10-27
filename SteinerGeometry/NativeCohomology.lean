import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheaf
import Mathlib.Basic.Complex.Basic

noncomputable section
namespace SteinerGeometry.EllipticCohomology
open CategoryTheory AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

abbrev H {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) (M : X.Modules) (q : ℕ) :=
  (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
    (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj M


end SteinerGeometry.EllipticCohomology
