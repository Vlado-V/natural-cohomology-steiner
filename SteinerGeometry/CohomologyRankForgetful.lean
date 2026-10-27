import SteinerGeometry.KernelNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor
import OAI.AlgebraicGeometry.SheafCohomology.AffineH

/-! Maximal rank of cohomology maps is independent of the chosen coefficient action. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SteinerGeometry.CohomologyRankForgetful

open CategoryTheory AlgebraicGeometry
open OAI.AlgebraicGeometry

universe u

/-- Restricting the coefficient action does not change the underlying map on
Zariski cohomology, hence does not change its maximal-rank predicate. -/
theorem coefficient_iff_zariski
    {X : Scheme.{u}} {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) (n : ℕ) {M N : X.Modules} (f : M ⟶ N) :
    HasMaximalRank
        ((AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
          c n).map f) ↔
      HasMaximalRank ((SheafCohomology.AffineH.Projective.zariskiFunctor X n).map f) :=
  Iff.rfl

end SteinerGeometry.CohomologyRankForgetful
