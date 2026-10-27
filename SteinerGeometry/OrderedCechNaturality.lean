module

public import SteinerGeometry.OrderedCechIdentification

set_option backward.privateInPublic true
@[expose] public section

/-! The original ordered base-linear Čech complex has a natural comparison
with actual sheaf cohomology in every positive degree. -/
noncomputable section
namespace SteinerGeometry.OrderedCechNaturality
open CategoryTheory AlgebraicGeometry
open OAI.AlgebraicGeometry
universe u

variable {X S : Scheme.{u}} [X.IsSeparated] (p : X ⟶ S)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
variable (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))

/-- Comparison on the actual original ordered complex, including its original
coefficient structure. -/
def positiveIso (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
      p M U).homology (n + 1) ≅
    (AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      p.appTop.hom (n + 1)).obj M :=
  AbelianModuli.HilbertConstruction.OrderedCech.ZariskiComparison.orderedCechZariskiModuleIso
    p.appTop.hom M U hU ha n

/-- Genuine cohomology maps commute with the original ordered Čech comparison. -/
theorem positiveIso_naturality {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) (n : ℕ) :
    HomologicalComplex.homologyMap
      ((SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor
        p U).map f) (n + 1) ≫ (positiveIso p U hU ha N n).hom =
    (positiveIso p U hU ha M n).hom ≫
      (AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
        p.appTop.hom (n + 1)).map f :=
  AbelianModuli.HilbertConstruction.OrderedCech.CohomologyNaturality.orderedCechZariskiModuleIso_naturality
    p.appTop.hom f U hU ha n

end SteinerGeometry.OrderedCechNaturality
