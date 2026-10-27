import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechComplex
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.CohomologyNaturality

/-! The two actual ordered Čech complexes are definitionally the same. -/
namespace SteinerGeometry.OrderedCechIdentification
open CategoryTheory AlgebraicGeometry
open OAI.AlgebraicGeometry
universe u

theorem presheaf_eq {X S : Scheme.{u}} (p : X ⟶ S) (M : X.Modules) :
    SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf p M =
      AbelianModuli.HilbertConstruction.Coefficient.ModulePresheaf.coefficientModulePresheaf
        p.appTop.hom M := rfl

theorem complex_eq {X S : Scheme.{u}} (p : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex p M U =
      AbelianModuli.HilbertConstruction.Ordered.CoefficientCechComplex.orderedCoefficientCechComplex
        p.appTop.hom M U := rfl

theorem complexFunctor_eq {X S : Scheme.{u}} (p : X ⟶ S)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor p U =
      AbelianModuli.HilbertConstruction.Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor
        p.appTop.hom U := rfl

theorem object_eq {X S : Scheme.{u}} (p : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechObject p M U n =
      AbelianModuli.HilbertConstruction.Ordered.CoefficientCechTerms.orderedCoefficientCechObject
        p.appTop.hom M U n := rfl

theorem map_f_eq {X S : Scheme.{u}} (p : X ⟶ S) {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    ((SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor
      p U).map f).f n =
    ((AbelianModuli.HilbertConstruction.Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor
      p.appTop.hom U).map f).f n := rfl

end SteinerGeometry.OrderedCechIdentification
